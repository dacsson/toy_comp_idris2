||| Parse assembly files
||| Resources:
||| - https://personal.cis.strath.ac.uk/jan.de-muijnck-hughes/temp-idris/cookbook/parsing.html
module Asm.Syntax

import Data.List
import Derive.Prelude
import Text.Lexer
import Text.Parser

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
-- │ OUTN  │ -     │ Mem  │ -    │
-- │ JMP   │ Label │ -    │ -    │
-- │ LABEL │ Label │ -    │ -    │
-- └───────┴───────┴──────┴──────┘

public export
MemLoc : Type
MemLoc = Nat -- TODO: Nat?

public export
data Memory = MemLocArg MemLoc
            | MemNameArg String
%runElab derive "Memory" [Show, Eq]

public export
data Imm = ImmArg Int
%runElab derive "Imm" [Show, Eq]

public export
data Label = LabelArg String
%runElab derive "Label" [Show, Eq, Ord]

public export
data Op = LI Memory Imm
         | MOV Memory Memory
         | ADD Memory Memory Memory
         | SUB Memory Memory Memory
         | MUL Memory Memory Memory
         | EQ Memory Memory Memory
         | LT Memory Memory Memory
         | LE Memory Memory Memory
         | JZ Label Memory
         | OUT Memory
         | OUTN Memory
         | JMP Label
         | LABEL Label
%runElab derive "Op" [Show, Eq]

||| Named collection of instructions
public export
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
               | TOUTN
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
    tokValue TOUTN _ = ()
    tokValue TJMP _ = ()
    tokValue TLABEL _ = ()
    tokValue TIgnore _ = ()

AsmToken : Type
AsmToken = Token AsmTokenKind

export
Show AsmToken where
    show (Tok kind text) = show "Token: " ++ show kind ++ " " ++ text

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
    ("OUTN", TOUTN),
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

memloc : AsmParser True Memory
memloc = do
    match TLBracket
    loc <- (MemLocArg <$> (cast <$> match TNum)) <|> (MemNameArg <$> match TIdentifier)
    match TRBracket
    pure loc

imm : AsmParser True Imm
imm = do
    match THashtag
    num <- match TNum
    pure $ ImmArg num

-- Could be ("@", Num)
label : AsmParser True Label
label = do
    match TAtSign
    name <- match TNum
    pure $ LabelArg (cast name)

parseLI : AsmParser True Op
parseLI = do
    match TLI
    arg1 <- memloc
    match TComma
    arg2 <- imm
    pure $ LI arg1 arg2

parseMOV : AsmParser True Op
parseMOV = do
    match TMOV
    arg1 <- memloc
    match TComma
    arg2 <- memloc
    pure $ MOV arg1 arg2

parseADD : AsmParser True Op
parseADD = do
    match TADD
    arg1 <- memloc
    match TComma
    arg2 <- memloc
    match TComma
    arg3 <- memloc
    pure $ ADD arg1 arg2 arg3

parseSUB : AsmParser True Op
parseSUB = do
    match TSUB
    arg1 <- memloc
    match TComma
    arg2 <- memloc
    match TComma
    arg3 <- memloc
    pure $ SUB arg1 arg2 arg3

parseMUL : AsmParser True Op
parseMUL = do
    match TMUL
    arg1 <- memloc
    match TComma
    arg2 <- memloc
    match TComma
    arg3 <- memloc
    pure $ MUL arg1 arg2 arg3

parseEQ : AsmParser True Op
parseEQ = do
    match TEQ
    arg1 <- memloc
    match TComma
    arg2 <- memloc
    match TComma
    arg3 <- memloc
    pure $ EQ arg1 arg2 arg3

parseLT : AsmParser True Op
parseLT = do
    match TLT
    arg1 <- memloc
    match TComma
    arg2 <- memloc
    match TComma
    arg3 <- memloc
    pure $ LT arg1 arg2 arg3

parseLE : AsmParser True Op
parseLE = do
    match TLE
    arg1 <- memloc
    match TComma
    arg2 <- memloc
    match TComma
    arg3 <- memloc
    pure $ LE arg1 arg2 arg3

parseJZ : AsmParser True Op
parseJZ = do
    match TJZ
    arg1 <- label
    match TComma
    arg2 <- memloc
    pure $ JZ arg1 arg2

parseOUT : AsmParser True Op
parseOUT = do
    match TOUT
    arg1 <- memloc
    pure $ OUT arg1

parseOUTN : AsmParser True Op
parseOUTN = do
    match TOUTN
    arg1 <- memloc
    pure $ OUTN arg1

parseJMP : AsmParser True Op
parseJMP = do
    match TJMP
    arg1 <- label
    pure $ JMP arg1

parseLABEL : AsmParser True Op
parseLABEL = do
    match TLABEL
    arg1 <- label
    pure $ LABEL arg1

instr : AsmParser True Op
instr = parseLI <|> parseMOV <|> parseADD <|> parseSUB <|> parseMUL
    <|> parseEQ <|> parseLT <|> parseLE <|> parseJZ <|> parseOUT <|> parseOUTN
    <|> parseJMP <|> parseLABEL

block : AsmParser True Block
block = do
    match TAtSign
    name <- match TNum -- (match TIdentifier <|> (cast <$> match TNum))
    match TColon
    instrs <- many instr
    pure $ MkBlock (LabelArg (cast name)) instrs

program : AsmParser False (List Block)
program = do
    -- first block doesnt have a label, so parse it manually
    intrs <- many instr
    blocks <- many block
    pure (MkBlock (LabelArg "start_") intrs :: blocks)

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
