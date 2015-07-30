{
module Parser where
import Data.Char
import Expression
}

%name parseExportFile
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

S : S Statement { $1 ++ [$2] }
  | {- empty -} { [] }

Statement : INT NS INT STR NL { StatementNS $1 $3 $4 } 
          | INT NI INT INT NL { StatementNI $1 $3 $4 }
          | INT US INT NL { StatementUS $1 $3 }
          | INT UM INT INT NL { StatementUM $1 $3 $4 }
          | INT UIM INT INT NL { StatementUIM $1 $3 $4 }
          | INT UP INT NL { StatementUP $1 $3 }
          | INT UG INT NL { StatementUG $1 $3 }
          | INT EV INT NL { StatementEV $1 $3 }
          | INT ES INT NL { StatementES $1 $3 }
          | INT EC INT IntList NL { StatementEC $1 $3 $4 }
          | INT EA INT INT NL { StatementEA $1 $3 $4 }
          | INT EL Info INT INT INT NL { StatementEL $1 $3 $4 $5 $6 }
          | INT EP Info INT INT INT NL { StatementEP $1 $3 $4 $5 $6 }
          | UNI INT NL { StatementUNI $2 }
          | DEF INT IntList BAR INT INT NL { StatementDEF $2 $3 $5 $6 }
          | AX INT IntList BAR INT NL { StatementAX $2 $3 $5 }
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

lexExportFile :: String -> [Token]
lexExportFile [] = []
lexExportFile (c:cs) 
    | c == '\n' = TokenNL : lexExportFile cs
    | c == '|' = TokenBAR : lexExportFile cs
    | isSpace c = lexExportFile cs
    | isDigit c = lexInt (c:cs)
    | otherwise = lexWord (c:cs)

lexInt cs = TokenInt (read num) : lexExportFile rest
      where (num,rest) = span isDigit cs

lexWord cs = case span (not . isSpace) cs of
    ("#NS",rest) -> TokenNS : lexExportFile rest
    ("#NI",rest) -> TokenNI : lexExportFile rest

    ("#US",rest) -> TokenUS : lexExportFile rest
    ("#UM",rest) -> TokenUM : lexExportFile rest
    ("#UIM",rest) -> TokenUIM : lexExportFile rest
    ("#UP",rest) -> TokenUP : lexExportFile rest
    ("#UG",rest) -> TokenUG : lexExportFile rest

    ("#EV",rest) -> TokenEV : lexExportFile rest
    ("#ES",rest) -> TokenES : lexExportFile rest
    ("#EC",rest) -> TokenEC : lexExportFile rest
    ("#EA",rest) -> TokenEA : lexExportFile rest
    ("#EL",rest) -> TokenEL : lexExportFile rest
    ("#EP",rest) -> TokenEP : lexExportFile rest

    ("#BD",rest) -> TokenBD : lexExportFile rest
    ("#BI",rest) -> TokenBI : lexExportFile rest
    ("#BS",rest) -> TokenBS : lexExportFile rest
    ("#BC",rest) -> TokenBC : lexExportFile rest

    ("#UNI",rest) -> TokenUNI : lexExportFile rest
    ("#DEF",rest) -> TokenDEF : lexExportFile rest
    ("#AX",rest) -> TokenAX : lexExportFile rest
    
    ("#BIND",rest) -> TokenBIND : lexExportFile rest
    ("#IND",rest) -> TokenIND : lexExportFile rest
    ("#INTRO",rest) -> TokenINTRO : lexExportFile rest
    ("#EIND",rest) -> TokenEIND : lexExportFile rest
    (str,rest) -> (TokenString str) : lexExportFile rest
    
--main = do
--  args <- getArgs
--  content <- readFile (args !! 0)
--  print . parseExportFile . lexExportFile $ content

}
