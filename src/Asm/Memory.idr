||| Memory-to-Memory ISA simulator

module Asm.Memory

import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Error.Either
import Derive.Prelude
import Data.SortedMap
import Asm.Syntax
import Data.List

%default total
%language ElabReflection

CpuMemory : Type
CpuMemory = SortedMap Nat Bits8

||| A state of mem2mem CPU
record CpuState where
    constructor MkCpuState
    ||| Infinite memory
    mem: CpuMemory
    labels: SortedMap Label Nat
    ||| A named locations are permitted
    namedLocations: SortedMap String Nat
    pc : Nat
%runElab derive "CpuState" [Show, Eq]

||| mem2mem CPU interpreter/simulator
Cpu : Type -> Type
Cpu = StateT CpuState (EitherT String IO)

nameToMem : String -> Cpu Nat
nameToMem name = do
    state <- gets namedLocations
    case SortedMap.lookup name state of
        Just addr => pure addr
        Nothing => lift $ throwE ("Unknown memory location: " ++ name)

readMem : Memory -> Cpu Bits8
readMem (MemLocArg addr) = do
    state <- gets mem
    case SortedMap.lookup addr state of
        Just val => pure val
        Nothing => lift $ throwE "Memory address out of bounds"
readMem (MemNameArg name) = do
    addr <- nameToMem name
    -- TODO: duplicate because if we recursively call readMem
    -- idris2 cant prove totality
    state <- gets mem
    case SortedMap.lookup addr state of
        Just val => pure val
        Nothing => lift $ throwE "Memory address out of bounds"

writeMem : Memory -> Bits8 -> Cpu ()
writeMem (MemLocArg addr) val = do
    -- Note: `$=` applies a function to the state field
    -- this is so cool, better then usual record update
    modify {mem $= SortedMap.insert addr val}
writeMem (MemNameArg name) val = do
    addr <- nameToMem name
    -- TODO: duplicate because if we recursively call writeMem
    -- idris2 cant prove totality
    modify {mem $= SortedMap.insert addr val}

jumpTo : Label -> Cpu ()
jumpTo label = do
    state <- gets labels
    case SortedMap.lookup label state of
        Just addr => modify {pc := addr}
        Nothing => lift $ throwE "Unknown label"

stepMem : Op -> Cpu ()
stepMem (LI addr (ImmArg val)) = writeMem addr (cast val)
stepMem (MOV dst src) = do
    val <- readMem src
    writeMem dst val
stepMem (ADD dst src1 src2) = do
    val1 <- readMem src1
    val2 <- readMem src2
    writeMem dst (cast (val1 + val2))
stepMem (SUB dst src1 src2) = do
    val1 <- readMem src1
    val2 <- readMem src2
    writeMem dst (cast (val1 - val2))
stepMem (MUL dst src1 src2) = do
    val1 <- readMem src1
    val2 <- readMem src2
    writeMem dst (cast (val1 * val2))
stepMem (EQ dst src1 src2) = do
    val1 <- readMem src1
    val2 <- readMem src2
    writeMem dst (if val1 == val2 then 1 else 0)
stepMem (LT dst src1 src2) = do
    val1 <- readMem src1
    val2 <- readMem src2
    writeMem dst (if val1 < val2 then 1 else 0)
stepMem (LE dst src1 src2) = do
    val1 <- readMem src1
    val2 <- readMem src2
    writeMem dst (if val1 <= val2 then 1 else 0)
stepMem (JZ (LabelArg label) src) = do
    val <- readMem src
    if val == 0
        then jumpTo (LabelArg label)
        else pure ()
stepMem (OUT src) = do
    val <- readMem src
    lift $ putStrLn (show val)
stepMem (LABEL (LabelArg label)) = pure ()
stepMem (JMP (LabelArg label)) = jumpTo (LabelArg label)

step : Op -> Cpu ()
step op = do
    modify {pc $= (+1)}
    stepMem op

covering
runOps : List Op -> Cpu ()
runOps ops = do
    pc <- gets pc
    case inBounds pc ops of
        Yes prf => do
            let op = List.index pc ops {ok = prf}
            step op
            runOps ops
        No _ => pure ()

||| Create a map of label -> ip for all labels in program
collectLabels : List Block -> SortedMap Label Nat
collectLabels blocks =
    snd $ foldl (\(ip, acc), b => (ip + (List.length b.instrs), SortedMap.insert b.name ip acc)) (0, labels) blocks
    where
        labels : SortedMap Label Nat
        labels = SortedMap.fromList [(LabelArg "start_", 0)]

getIfNamed : Memory -> Maybe String
getIfNamed (MemNameArg name) = Just name
getIfNamed _ = Nothing

||| Return all memory operands in an instruction.
getMemoryArgs : Op -> List Memory
getMemoryArgs (LI arg _) = [arg]
getMemoryArgs (MOV arg1 arg2) = [arg1, arg2]
getMemoryArgs (ADD arg1 arg2 arg3) = [arg1, arg2, arg3]
getMemoryArgs (SUB arg1 arg2 arg3) = [arg1, arg2, arg3]
getMemoryArgs (MUL arg1 arg2 arg3) = [arg1, arg2, arg3]
getMemoryArgs (EQ arg1 arg2 arg3) = [arg1, arg2, arg3]
getMemoryArgs (LT arg1 arg2 arg3) = [arg1, arg2, arg3]
getMemoryArgs (LE arg1 arg2 arg3) = [arg1, arg2, arg3]
getMemoryArgs (JZ _ arg) = [arg]
getMemoryArgs (OUT arg) = [arg]
getMemoryArgs _ = []

||| Allocate distinct addresses for names after all numeric addresses.
collectNamedLocs : List Block -> SortedMap String Nat
collectNamedLocs blocks =
    let operands = concatMap getMemoryArgs (concatMap (.instrs) blocks)
        names = nub (mapMaybe getIfNamed operands)
        firstFree = foldl nextAddress 0 operands
    in snd $ foldl allocate (firstFree, SortedMap.empty) names
    where
        nextAddress : Nat -> Memory -> Nat
        nextAddress next (MemLocArg addr) = max next (S addr)
        nextAddress next (MemNameArg _) = next

        allocate : (Nat, SortedMap String Nat) -> String -> (Nat, SortedMap String Nat)
        allocate (addr, locations) name =
            (S addr, SortedMap.insert name addr locations)

runMemCpu : Cpu a -> IO (Either String (CpuState, a))
runMemCpu a = runEitherT $ runStateT initialState a
    where
        initialState : CpuState
        initialState = MkCpuState emptyMem emptyLabels emptyNamedLocs 0
            where
                emptyMem : CpuMemory
                emptyMem = SortedMap.empty
                emptyLabels : SortedMap Label Nat
                emptyLabels = SortedMap.empty
                emptyNamedLocs : SortedMap String Nat
                emptyNamedLocs = SortedMap.empty

export
covering
runCpu : List Block -> IO (Either String (CpuState, ()))
runCpu blocks = runMemCpu $ do
    modify {labels := collectLabels blocks}
    modify {namedLocations := collectNamedLocs blocks}
    modify {pc := 0}
    runOps instrs
    where
        instrs = concatMap (.instrs) blocks
