{
module Parser where
import Data.Char
import Expression
}

%name parseStatement
%tokentype { Token }
%error { parseError }

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

parseError :: [Token] -> a
parseError tokens = error $ "ERROR: " ++ show tokens

lexStatement :: String -> [Token]
lexStatement [] = []
lexStatement (c:cs) 
    | c == '\n' = TokenNL : lexStatement cs
    | c == '|' = TokenBAR : lexStatement cs
    | isSpace c = lexStatement cs
    | isDigit c = lexInt (c:cs)
    | otherwise = lexWord (c:cs)

lexInt cs = TokenInt (read num) : lexStatement rest
      where (num,rest) = span isDigit cs

lexWord cs = case span (not . isSpace) cs of
    ("#NS",rest) -> TokenNS : lexStatement rest
    ("#NI",rest) -> TokenNI : lexStatement rest

    ("#US",rest) -> TokenUS : lexStatement rest
    ("#UM",rest) -> TokenUM : lexStatement rest
    ("#UIM",rest) -> TokenUIM : lexStatement rest
    ("#UP",rest) -> TokenUP : lexStatement rest
    ("#UG",rest) -> TokenUG : lexStatement rest

    ("#EV",rest) -> TokenEV : lexStatement rest
    ("#ES",rest) -> TokenES : lexStatement rest
    ("#EC",rest) -> TokenEC : lexStatement rest
    ("#EA",rest) -> TokenEA : lexStatement rest
    ("#EL",rest) -> TokenEL : lexStatement rest
    ("#EP",rest) -> TokenEP : lexStatement rest

    ("#BD",rest) -> TokenBD : lexStatement rest
    ("#BI",rest) -> TokenBI : lexStatement rest
    ("#BS",rest) -> TokenBS : lexStatement rest
    ("#BC",rest) -> TokenBC : lexStatement rest

    ("#UNI",rest) -> TokenUNI : lexStatement rest
    ("#DEF",rest) -> TokenDEF : lexStatement rest
    ("#AX",rest) -> TokenAX : lexStatement rest
    
    ("#BIND",rest) -> TokenBIND : lexStatement rest
    ("#IND",rest) -> TokenIND : lexStatement rest
    ("#INTRO",rest) -> TokenINTRO : lexStatement rest
    ("#EIND",rest) -> TokenEIND : lexStatement rest
    (str,rest) -> (TokenString str) : lexStatement rest
    
--main = do
--  args <- getArgs
--  content <- readFile (args !! 0)
--  print . parseExportFile . lexStatement $ content

}
