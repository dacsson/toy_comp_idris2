||| Parse assembly files
||| Resources:
||| - https://personal.cis.strath.ac.uk/jan.de-muijnck-hughes/temp-idris/cookbook/parsing.html
module Memory.Syntax

import Data.List
import Derive.Prelude
import Data.List1
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
-- │ JMP   │ Label │ -    │ -    │
-- │ LABEL │ Label │ -    │ -    │
-- └───────┴───────┴──────┴──────┘

MemLoc : Type
MemLoc = Nat

Imm : Type
Imm = Int

Label : Type
Label = String

data Op = LI MemLoc Imm
         | MOV MemLoc MemLoc
         | ADD MemLoc MemLoc MemLoc
         | SUB MemLoc MemLoc MemLoc
         | MUL MemLoc MemLoc MemLoc
         | EQ MemLoc MemLoc MemLoc
         | LT MemLoc MemLoc MemLoc
         | LE MemLoc MemLoc MemLoc
         | JZ Label MemLoc
         | OUT MemLoc
         | JMP Label
         | LABEL Label
%runElab derive "Op" [Show, Eq]

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
AsmTokenMap = toTokenMap [(spaces, TIgnore)] ++
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
    ] ++ [(alphaNum <+> many alphaNum, \s => Tok TNum s)]

public export
lexAsm : String -> Maybe (List (WithBounds AsmToken))
lexAsm str =
    case lex AsmTokenMap str of
        (tokens, _, _, "") => Just $ filter (not . ignored) tokens
        _ => Nothing

op : Grammar state AsmToken True Op
op = ?process

