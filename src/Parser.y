{
{-|
Module      : Parser
Description : Parse the Lean kernel export format
Copyright   : (c) Daniel Selsam, 2015
License     : GPL-3
Maintainer  : daniel.selsam@gmail.com

Parse the Lean kernel export format
-}
module Parser (parse_statement,lex_statement,Statement (..), IDecl (..), IIntro (..)) where
import Data.Char
import Expression
}

%name parse_statement
%tokentype { Token }
%error { parse_error }

%token 
NS { TokenNS }
NI { TokenNI }

US { TokenUS }
UM { TokenUM }
UIM { TokenUIM }
UP { TokenUP }
UG { TokenUG }

EV { TokenEV }
ES { TokenES }
EC { TokenEC }
EA { TokenEA }
EL { TokenEL }
EP { TokenEP }

BD { TokenBD }
BI { TokenBI }
BS { TokenBS }
BC { TokenBC }

UNI { TokenUNI }
DEF { TokenDEF }
AX { TokenAX }

BIND { TokenBIND }
IND { TokenIND }
INTRO { TokenINTRO }
EIND { TokenEIND }
INT { TokenInt $$ }
STR { TokenString $$ }

BAR { TokenBAR }
NL { TokenNL }
%%

S : INT NS INT STR { StatementNS $1 $3 $4 } 
  | INT NI INT INT { StatementNI $1 $3 $4 }
  | INT US INT { StatementUS $1 $3 }
  | INT UM INT INT { StatementUM $1 $3 $4 }
  | INT UIM INT INT { StatementUIM $1 $3 $4 }
  | INT UP INT { StatementUP $1 $3 }
  | INT UG INT { StatementUG $1 $3 }
  | INT EV INT { StatementEV $1 $3 }
  | INT ES INT { StatementES $1 $3 }
  | INT EC INT IntList { StatementEC $1 $3 $4 }
  | INT EA INT INT { StatementEA $1 $3 $4 }
  | INT EL Info INT INT INT { StatementEL $1 $3 $4 $5 $6 }
  | INT EP Info INT INT INT { StatementEP $1 $3 $4 $5 $6 }
  | UNI INT { StatementUNI $2 }
  | DEF INT IntList BAR INT INT { StatementDEF $2 $3 $5 $6 }
  | AX INT IntList BAR INT { StatementAX $2 $3 $5 }
  | BIND INT INT IntList NL Inds EIND NL { StatementBIND $2 $3 $4 $6 }

Info : BD { BinderDefault }
     | BI { BinderImplicit }
     | BS { BinderStrict }
     | BC { BinderClass }

IntList : IntList INT { $1 ++ [$2] }
        | {- empty -} { [] }
          
Inds : Inds IND INT INT NL IntroList { $1 ++ [IDecl $3 $4 $6] }
     | {- empty -} { [] }

IntroList : IntroList INTRO INT INT NL { $1 ++ [IIntro $3 $4] }
          | {- empty -} { [] }

{

data Token = TokenNS | TokenNI 
    | TokenUS | TokenUM | TokenUIM | TokenUP | TokenUG 
    | TokenEV | TokenES | TokenEC | TokenEA | TokenEL | TokenEP
    | TokenBD | TokenBI | TokenBS | TokenBC
    | TokenUNI | TokenDEF | TokenAX
    | TokenBIND | TokenIND | TokenINTRO | TokenEIND | TokenInt Integer | TokenString String 
    | TokenBAR | TokenNL deriving (Show)

data Statement = StatementNS Integer Integer String
    | StatementNI Integer Integer Integer

    | StatementUS Integer Integer
    | StatementUM Integer Integer Integer
    | StatementUIM Integer Integer Integer
    | StatementUP Integer Integer
    | StatementUG Integer Integer
    
    | StatementEV Integer Integer
    | StatementES Integer Integer
    | StatementEC Integer Integer [Integer]
    | StatementEA Integer Integer Integer
    | StatementEL Integer BinderInfo Integer Integer Integer
    | StatementEP Integer BinderInfo Integer Integer Integer
    
    | StatementUNI Integer
    | StatementDEF Integer [Integer] Integer Integer
    | StatementAX Integer [Integer] Integer
    | StatementBIND Integer Integer [Integer] [IDecl]
    deriving (Show)

data IDecl = IDecl Integer Integer [IIntro] deriving (Show)
data IIntro = IIntro Integer Integer deriving (Show)

parse_error :: [Token] -> a
parse_error tokens = error $ "parse error"

lex_statement :: String -> [Token]
lex_statement [] = []
lex_statement (c:cs) 
    | c == '\n' = TokenNL : lex_statement cs
    | c == '|' = TokenBAR : lex_statement cs
    | isSpace c = lex_statement cs
    | isDigit c = lex_int (c:cs)
    | otherwise = lex_word (c:cs)

lex_int cs = TokenInt (read num) : lex_statement rest
      where (num,rest) = span isDigit cs

lex_word cs = case span (not . isSpace) cs of
    ("#NS",rest) -> TokenNS : lex_statement rest
    ("#NI",rest) -> TokenNI : lex_statement rest

    ("#US",rest) -> TokenUS : lex_statement rest
    ("#UM",rest) -> TokenUM : lex_statement rest
    ("#UIM",rest) -> TokenUIM : lex_statement rest
    ("#UP",rest) -> TokenUP : lex_statement rest
    ("#UG",rest) -> TokenUG : lex_statement rest

    ("#EV",rest) -> TokenEV : lex_statement rest
    ("#ES",rest) -> TokenES : lex_statement rest
    ("#EC",rest) -> TokenEC : lex_statement rest
    ("#EA",rest) -> TokenEA : lex_statement rest
    ("#EL",rest) -> TokenEL : lex_statement rest
    ("#EP",rest) -> TokenEP : lex_statement rest

    ("#BD",rest) -> TokenBD : lex_statement rest
    ("#BI",rest) -> TokenBI : lex_statement rest
    ("#BS",rest) -> TokenBS : lex_statement rest
    ("#BC",rest) -> TokenBC : lex_statement rest

    ("#UNI",rest) -> TokenUNI : lex_statement rest
    ("#DEF",rest) -> TokenDEF : lex_statement rest
    ("#AX",rest) -> TokenAX : lex_statement rest
    
    ("#BIND",rest) -> TokenBIND : lex_statement rest
    ("#IND",rest) -> TokenIND : lex_statement rest
    ("#INTRO",rest) -> TokenINTRO : lex_statement rest
    ("#EIND",rest) -> TokenEIND : lex_statement rest
    (str,rest) -> (TokenString str) : lex_statement rest
    
}
