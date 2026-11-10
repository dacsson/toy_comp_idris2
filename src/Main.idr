module Main

import System
import System.Console.GetOpt
import System.File
import Text.Bounded
import Derive.Prelude
import Asm.Syntax
import Asm.Memory

%language ElabReflection

data ExecMode = Memory | Stack | Register | Compile | None
%runElab derive "ExecMode" [Show]

modeFromString : String -> ExecMode
modeFromString "memory" = Memory
modeFromString "stack" = Stack
modeFromString "register" = Register
modeFromString "compile" = Compile
modeFromString _ = None

data Args = Mode ExecMode | File String
%runElab derive "Args" [Show]

opts : List (OptDescr Args)
opts = [
    MkOpt ['m'] ["mode"] (ReqArg (Mode . modeFromString) "MODE") "Execution mode (memory, stack, register, compile)",
    MkOpt ['i'] ["input"] (ReqArg File "FILE") "Input file"
]

usage : String
usage = usageInfo "Usage: toy_comp_idris2 --mode=MODE --input=FILE" opts

main : IO ()
main = do
    args <- getArgs
    let result = getOpt Permute opts args

    case (GetOpt.Result.options result) of
        -- I wish i could do `| [(File file), (Mode mode)]` so combine patterns
        -- but maybe i just dont know how to?
        [(Mode mode), (File file)] => do
            contents <- readFile file

            case contents of
                Left err => putStrLn $ "failed to read file: " ++ show err
                Right contents => do
                    case mode of
                        Memory => case parse contents of
                            Left err => putStrLn $ "failed to parse: " ++ err
                            Right blocks => do
                                res <- Memory.runCpu blocks
                                case res of
                                    Left err => (ignore $ fPutStrLn stderr ("Error: " ++ err)) >> exitFailure
                                    Right _ => pure ()
                        _ => putStrLn $ "not implemented: " ++ show mode
        _ => putStrLn usage
