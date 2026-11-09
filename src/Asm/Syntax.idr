||| Parse assembly files
||| Resources:
||| - https://personal.cis.strath.ac.uk/jan.de-muijnck-hughes/temp-idris/cookbook/parsing.html
module Asm.Syntax

import Data.List
import Derive.Prelude
import Data.List1
import Text.Lexer
import Text.Parser
import Debug.Trace

%default total
%language ElabReflection

-- ISA:
-- ┌───────┬───────┬──────┬──────┐
-- │ op    │ dst   │ src1 │ src2 │
-- ├───────┼───────┼──────┼──────┤
-- │ LI    │ Mem   │ Imm  │ -    │
-- │ MOV   │ Mem   │ Mem  │ -    │
-- │ ADD   │ Mem   │ Mem  │ Mem  │
-- │ SUB   │ Mem   │ Mem  │ Mem  │
-- │ MUL   │ Mem   │ Mem  │ Mem  │
-- │ EQ    │ Mem   │ Mem  │ Mem  │
-- │ LT    │ Mem   │ Mem  │ Mem  │
-- │ LE    │ Mem   │ Mem  │ Mem  │
-- │ JZ    │ Label │ Mem  │ -    │
-- │ OUT   │ -     │ Mem  │ -    │
-- │ JMP   │ Label │ -    │ -    │
-- │ LABEL │ Label │ -    │ -    │
-- └───────┴───────┴──────┴──────┘

MemLoc : Type
MemLoc = Int -- TODO: Nat?

Imm : Type
Imm = Int

Label : Type
Label = String

data AsmArg = MemLocArg MemLoc
         | ImmArg Imm
         | LabelArg Label
%runElab derive "AsmArg" [Show, Eq]

data Op = LI AsmArg AsmArg
         | MOV AsmArg AsmArg
         | ADD AsmArg AsmArg AsmArg
         | SUB AsmArg AsmArg AsmArg
         | MUL AsmArg AsmArg AsmArg
         | EQ AsmArg AsmArg AsmArg
         | LT AsmArg AsmArg AsmArg
         | LE AsmArg AsmArg AsmArg
         | JZ AsmArg AsmArg
         | OUT AsmArg
         | JMP AsmArg
         | LABEL AsmArg
%runElab derive "Op" [Show, Eq]

||| Named collection of instructions
record Block where
    constructor MkBlock
    name : Label
    instrs : List Op
%runElab derive "Block" [Show, Eq]

data AsmTokenKind = TAtSign -- @
               | TComma -- ,
               | TColon -- :
               | TRBracket -- ]
               | TLBracket -- [
               | THashtag -- #
               | TIdentifier
               | TNum
               | TLI
               | TMOV
               | TADD
               | TSUB
               | TMUL
               | TEQ
               | TLT
               | TLE
               | TJZ
               | TOUT
               | TJMP
               | TLABEL
               | TIgnore -- whitespace etc.
%runElab derive "AsmTokenKind" [Show, Eq]

TokenKind AsmTokenKind where
    TokType TIdentifier = String
    TokType TNum = Int
    TokType _ = ()

    tokValue TAtSign _ = ()
    tokValue TComma _ = ()
    tokValue TColon _ = ()
    tokValue TRBracket _ = ()
    tokValue TLBracket _ = ()
    tokValue THashtag _ = ()
    tokValue TIdentifier s = s
    tokValue TNum n = cast n
    tokValue TLI _ = ()
    tokValue TMOV _ = ()
    tokValue TADD _ = ()
    tokValue TSUB _ = ()
    tokValue TMUL _ = ()
    tokValue TEQ _ = ()
    tokValue TLT _ = ()
    tokValue TLE _ = ()
    tokValue TJZ _ = ()
    tokValue TOUT _ = ()
    tokValue TJMP _ = ()
    tokValue TLABEL _ = ()
    tokValue TIgnore _ = ()

AsmToken : Type
AsmToken = Token AsmTokenKind

export
Show AsmToken where
    show (Tok kind text) = show "Token: " ++ show kind ++ " " ++ text

||| Construct concrete Op from opcode token and arbitrary args
MkOp : AsmTokenKind -> List1 AsmArg -> Maybe Op
MkOp opcode args = do
    -- Split by argument count of different opcodes
    -- TODO: verify types of arguments
    trace ("[MkOp] " ++ show opcode ++ " " ++ show args) $ case args of
        (arg1 ::: [arg2]) => case opcode of
            TLI => Just (LI arg1 arg2)
            TMOV => Just (MOV arg1 arg2)
            TJZ => Just (JZ arg1 arg2)
            _ => Nothing
        (arg1 ::: arg2 :: [arg3]) => case opcode of
            TADD => Just (ADD arg1 arg2 arg3)
            TSUB => Just (SUB arg1 arg2 arg3)
            TMUL => Just (MUL arg1 arg2 arg3)
            TEQ => Just (EQ arg1 arg2 arg3)
            TLT => Just (LT arg1 arg2 arg3)
            TLE => Just (LE arg1 arg2 arg3)
            _ => Nothing
        (arg1 ::: []) => case opcode of
            TOUT => Just (OUT arg1)
            TJMP => Just (JMP arg1)
            TLABEL => Just (LABEL arg1)
            _ => Nothing
        _ => Nothing

keywords : List (String, AsmTokenKind)
keywords = [
    ("LI", TLI),
    ("MOV", TMOV),
    ("ADD", TADD),
    ("SUB", TSUB),
    ("MUL", TMUL),
    ("EQ", TEQ),
    ("LT", TLT),
    ("LE", TLE),
    ("JZ", TJZ),
    ("OUT", TOUT),
    ("JMP", TJMP),
    ("LABEL", TLABEL)
]

ignored : WithBounds AsmToken -> Bool
ignored (MkBounded (Tok TIgnore _) _ _) = True
ignored _ = False

||| A mapping from lexers to token generating functions
AsmTokenMap : TokenMap AsmToken
AsmTokenMap = toTokenMap [(spaces <|> newlines, TIgnore)] ++
    -- Technically we dont have real identifiers but who cares lol
    [(alpha <+> many alphaNum, \s =>
        case lookup s keywords of
            Just kind => Tok kind s
            Nothing => Tok TIdentifier s
    )] ++ toTokenMap [
        (exact "@", TAtSign),
        (exact ",", TComma),
        (exact ":", TColon),
        (exact "[", TLBracket),
        (exact "]", TRBracket),
        (exact "#", THashtag)
    ] ++ [(intLit, \s => Tok TNum s)]

public export
lexAsm : String -> Maybe (List (WithBounds AsmToken))
lexAsm str =
    case lex AsmTokenMap str of
        (tokens, _, _, "") => Just $ filter (not . ignored) tokens
        _ => Nothing

||| A stateful asm parser, wrapper for Text.Parser.Grammer
AsmParser : (consumes: Bool) -> (result: Type) -> Type
AsmParser consumes result = Grammar () AsmToken consumes result

memloc : AsmParser True AsmArg
memloc = do
    match TLBracket
    num <- match TNum
    match TRBracket
    pure $ MemLocArg num

imm : AsmParser True AsmArg
imm = do
    match THashtag
    num <- match TNum
    pure $ ImmArg num

-- Could be ("@", Num)
label : AsmParser True AsmArg
label = do
    match TAtSign
    name <- match TNum -- (match TIdentifier <|> (cast <$> match TNum))
    pure $ LabelArg (cast name)

arg : AsmParser True AsmArg
arg = memloc <|> imm <|> label

args : AsmParser True (List1 AsmArg)
args = traceVal <$> sepBy1 (match TComma) arg
    -- first <- arg
    -- rest <- many arg
    -- pure (first :: rest)

opcode : AsmParser True AsmTokenKind
opcode = terminal "Expected opcode" $ \t => traceVal <$> (case Token.kind t of
    TLI => Just TLI
    TMOV => Just TMOV
    TADD => Just TADD
    TSUB => Just TSUB
    TMUL => Just TMUL
    TEQ => Just TEQ
    TLT => Just TLT
    TLE => Just TLE
    TJZ => Just TJZ
    TOUT => Just TOUT
    TJMP => Just TJMP
    TLABEL => Just TLABEL
    _ => Nothing)

instr : AsmParser True Op
instr = do
    op <- opcode
    arguments <- args
    terminal "Expected opcode" $ \_ => trace ("[instr] " ++ show op ++ " " ++ show arguments) $ MkOp op arguments

block : AsmParser True Block
block = do
    trace "[block] parse TAtSign" $ match TAtSign
    name <- traceVal <$> match TNum -- (match TIdentifier <|> (cast <$> match TNum))
    trace "[block] parse TColon" $ match TColon
    instrs <- many instr
    pure $ MkBlock (cast name) instrs

program : AsmParser False (List Block)
program = do
    -- first block doesnt have a label, so parse it manually
    intrs <- traceVal <$> many instr
    blocks <- many block
    pure (MkBlock "start_" intrs :: blocks)

parseAsm : List (WithBounds AsmToken) -> Either String (List Block)
parseAsm toks = case parse program $ filter (not . ignored) toks of
    Right (l, []) => Right l
    Right e => Left $ "contains tokens that were not consumed" ++ show e
    Left e => Left (show e)

export
parse : String -> Either String (List Block)
parse src = case lexAsm src of
    Just toks => parseAsm toks
    Nothing => Left "lex error"
