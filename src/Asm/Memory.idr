||| Memory-to-Memory ISA simulator

module Asm.Memory

import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Error.Either
import Derive.Prelude
import Data.SortedMap
import Asm.Syntax

%default total
%language ElabReflection

Memory : Type
Memory = SortedMap Nat Bits8

||| A state of mem2mem CPU
record CpuState where
    constructor MkCpuState
    ||| Infinite memory
    mem: Memory
    ||| A named locations are permitted
    namedLocations: SortedMap String Nat
    pc : Nat
%runElab derive "CpuState" [Show, Eq]

||| mem2mem CPU interpreter/simulator
Cpu : Type -> Type
Cpu = StateT CpuState (EitherT String IO)

readMem : Nat -> Cpu Bits8
readMem addr = do
    state <- gets mem
    case SortedMap.lookup addr state of
        Just val => pure val
        Nothing => lift $ throwE "Memory address out of bounds"

writeMem : Nat -> Bits8 -> Cpu ()
writeMem addr val = do
    -- Note: `$=` applies a function to the state field
    -- this is so cool, better then usual record update
    modify {mem $= SortedMap.insert addr val}

nameToMem : String -> Cpu Nat
nameToMem name = do
    state <- gets namedLocations
    case SortedMap.lookup name state of
        Just addr => pure addr
        Nothing => lift $ throwE "Unknown memory location"

stepMem : Cpu ()
stepMem
