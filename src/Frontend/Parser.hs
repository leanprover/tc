{-# LANGUAGE TemplateHaskell #-}
module Frontend.Parser where

import System.Environment
import Text.Parsec

import Kernel.Name
import Kernel.Level
import Kernel.Expr

import Kernel.TypeChecker
import Kernel.Inductive

import Control.Monad
import qualified Control.Monad.State as S
import Control.Monad.Reader
import Control.Monad.Trans.Except

import Numeric
import Lens.Simple (makeLenses, view, over, use, uses, (%=), (.=), (<~), (+=))

import qualified Data.Map as Map
import Data.Map (Map)

import qualified Data.Set as Set
import Data.Set (Set)

import Debug.Trace
data IdxType = IdxName | IdxLevel | IdxExpr | IdxUni deriving (Show)

data ExportError = RepeatedIdx IdxType
                 | UnknownIdx IdxType
                 | TError TypeError -- TODO(dhs): import qualified
                 | IDeclError IndDeclError deriving (Show)

data Context = Context {
  _ctxNameMap :: Map Integer Name,
  _ctxLevelMap :: Map Integer Level,
  _ctxExprMap :: Map Integer Expr,
  _ctxEnv :: Env,
  _ctxDefId :: Integer,
  _ctxIndId :: Integer
  }

makeLenses ''Context

blank = char ' '

mkStdContext = Context (Map.insert 0 noName Map.empty) (Map.insert 0 mkZero Map.empty) Map.empty mkStdEnv 0 0

type ParserMethod = ParsecT String () (ExceptT ExportError (S.State Context))

parseInteger :: ParserMethod Integer
parseInteger = do
  digits <- many1 digit
  return . fst $ ((readDec digits)!!0)

parseInt :: ParserMethod Int
parseInt = liftM read (many1 digit)

assertUndefined :: Integer -> IdxType -> Map Integer a -> ExceptT ExportError (S.State Context) ()
assertUndefined idx idxType m = if Map.member idx m then throwE (RepeatedIdx idxType) else return ()

parseExportFile :: ParserMethod ()
parseExportFile = sepEndBy1 parseStatement newline >> eof
  where
    parseStatement :: ParserMethod ()
    parseStatement = do
      try parseDefinition <|> parseValue

    parseDefinition :: ParserMethod ()
    parseDefinition = try parseUNI <|> try parseDEF <|> try parseAX <|> parseIND

    parseUNI :: ParserMethod ()
    parseUNI = do
      string "#UNI" >> blank
      nameIdx <- parseInteger
      lift $ do
        name <- uses ctxNameMap (Map.! nameIdx)
        alreadyPresent <- uses ctxEnv (envHasGlobalLevel name)
        if alreadyPresent
        then throwE $ RepeatedIdx IdxUni
        else ctxEnv %= envAddGlobalLevel name

    parseDEF :: ParserMethod ()
    parseDEF = do
      string "#DEF" >> blank
      nameIdx <- parseInteger <* blank
      lpNameIdxs <- (endBy parseInteger blank) <* string "| "
      typeIdx <- parseInteger <* blank
      valueIdx <- parseInteger
      lift $ do
        name <- uses ctxNameMap (Map.! nameIdx)
        lpNames <- uses ctxNameMap (\m -> map (m Map.!) lpNameIdxs)
        ty <- uses ctxExprMap (Map.! typeIdx)
        val <- uses ctxExprMap (Map.! valueIdx)
        ctxDefId += 1
        env <- use ctxEnv
        use ctxDefId >>= (\did -> trace ("DEF(" ++ show did ++ "): " ++ show name) (return ()))
        case envAddDefinition name lpNames ty val env of
          Left err -> throwE $ TError err
          Right env -> ctxEnv .= env

    parseAX :: ParserMethod ()
    parseAX = do
      string "#AX" >> blank
      nameIdx <- parseInteger <* blank
      lpNameIdxs <- (endBy parseInteger blank) <* string "| "
      typeIdx <- parseInteger
      lift $ do
        name <- uses ctxNameMap (Map.! nameIdx)
        lpNames <- uses ctxNameMap (\m -> map (m Map.!) lpNameIdxs)
        ty <- uses ctxExprMap (Map.! typeIdx)
        ctxDefId += 1
        use ctxDefId >>= (\did -> trace ("AX(" ++ show did ++ "): " ++ show name) (return ()))
        env <- use ctxEnv
        case envAddAxiom name lpNames ty env of
          Left err -> throwE $ TError err
          Right env -> ctxEnv .= env

    parseIND :: ParserMethod ()
    parseIND = do
      string "#IND" >> blank
      numParams <- parseInt <* blank
      lpNameIdxs <- (endBy parseInteger blank) <* string "| "
      indNameIdx <- parseInteger <* blank
      indTypeIdx <- parseInteger <* blank
      numIntroRules <- parseInt
      introRules <- count numIntroRules parseIntroRule
      lift $ do
        indName <- uses ctxNameMap (Map.! indNameIdx)
        lpNames <- uses ctxNameMap (\m -> map (m Map.!) lpNameIdxs)
        indType <- uses ctxExprMap (Map.! indTypeIdx)
        ctxIndId += 1
        use ctxIndId >>= (\did -> trace ("IND(" ++ show did ++ "): " ++ show indName) (return ()))
        env <- use ctxEnv
        case addInductive env (IndDecl numParams lpNames indName indType introRules) of
          Left err -> throwE $ IDeclError err
          Right env -> ctxEnv .= env

    parseIntroRule :: ParserMethod IntroRule
    parseIntroRule = do
      newline
      string "#INTRO" >> blank
      irNameIdx <- parseInteger <* blank
      irTypeIdx <- parseInteger
      lift $ do
        irName <- uses ctxNameMap (Map.! irNameIdx)
        irType <- uses ctxExprMap (Map.! irTypeIdx)
        return $ IntroRule irName irType

    parseValue :: ParserMethod ()
    parseValue = do
      try parseN <|> try parseU <|> parseE

    parseN = try parseNI <|> parseNS
    parseU = try parseUS <|> try parseUM <|> try parseUIM <|> try parseUP <|> parseUG
    parseE = try parseEV <|> try parseES <|> try parseEC <|> try parseEA <|> try parseEL <|> parseEP

    parseNI = do
      newIdx <- parseInteger <* blank
      string "#NI" >> blank
      oldIdx <- parseInteger <* blank
      i <- parseInteger
      lift $ do
        use ctxNameMap >>= assertUndefined newIdx IdxName
        ctxNameMap <~ (uses ctxNameMap (\m -> Map.insert newIdx (nameRConsI (m Map.! oldIdx) i) m))

    parseNS = do
      newIdx <- parseInteger <* blank
      string "#NS" >> blank
      oldIdx <- parseInteger <* blank
      s <- manyTill anyChar (lookAhead newline)
      lift $ do
        use ctxNameMap >>= assertUndefined newIdx IdxName
        ctxNameMap <~ (uses ctxNameMap (\m -> Map.insert newIdx (nameRConsS (m Map.! oldIdx) s) m))

    parseUS = do
      newIdx <- parseInteger <* blank
      string "#US" >> blank
      oldIdx <- parseInteger
      s <- many (blank *> alphaNum)
      lift $ do
        use ctxLevelMap >>= assertUndefined newIdx IdxLevel
        ctxLevelMap <~ (uses ctxLevelMap (\m -> Map.insert newIdx (mkSucc (m Map.! oldIdx)) m))

    parseUM = do
      newIdx <- parseInteger <* blank
      string "#UM" >> blank
      lhsIdx <- parseInteger <* blank
      rhsIdx <- parseInteger
      lift $ do
        use ctxLevelMap >>= assertUndefined newIdx IdxLevel
        ctxLevelMap <~ (uses ctxLevelMap (\m -> Map.insert newIdx (mkMax (m Map.! lhsIdx) (m Map.! rhsIdx)) m))

    parseUIM = do
      newIdx <- parseInteger <* blank
      string "#UIM" >> blank
      lhsIdx <- parseInteger <* blank
      rhsIdx <- parseInteger
      lift $ do
        use ctxLevelMap >>= assertUndefined newIdx IdxLevel
        ctxLevelMap <~ (uses ctxLevelMap (\m -> Map.insert newIdx (mkIMax (m Map.! lhsIdx) (m Map.! rhsIdx)) m))

    parseUP = do
      newIdx <- parseInteger <* blank
      string "#UP" >> blank
      nameIdx <- parseInteger
      lift $ do
        use ctxLevelMap >>= assertUndefined newIdx IdxLevel
        name <- uses ctxNameMap (Map.! nameIdx)
        ctxLevelMap %= Map.insert newIdx (mkLevelParam name)

    parseUG = do
      newIdx <- parseInteger <* blank
      string "#UG" >> blank
      nameIdx <- parseInteger
      lift $ do
        use ctxLevelMap >>= assertUndefined newIdx IdxLevel
        name <- uses ctxNameMap (Map.! nameIdx)
        ctxLevelMap %= Map.insert newIdx (mkGlobalLevel name)

    parseEV = do
      newIdx <- parseInteger <* blank
      string "#EV" >> blank
      varIdx <- parseInt
      lift $ do
        use ctxExprMap >>= assertUndefined newIdx IdxExpr
        ctxExprMap %= Map.insert newIdx (mkVar varIdx)

    parseES = do
      newIdx <- parseInteger <* blank
      string "#ES" >> blank
      levelIdx <- parseInteger
      lift $ do
        use ctxExprMap >>= assertUndefined newIdx IdxExpr
        level <- uses ctxLevelMap (Map.! levelIdx)
        ctxExprMap %= Map.insert newIdx (mkSort level)

    parseEC = do
      newIdx <- parseInteger <* blank
      string "#EC" >> blank
      nameIdx <- parseInteger
      levelIdxs <- many (blank *> parseInteger)
      lift $ do
        use ctxExprMap >>= assertUndefined newIdx IdxExpr
        name <- uses ctxNameMap (Map.! nameIdx)
        levels <- uses ctxLevelMap (\m -> map (m Map.!) levelIdxs)
        ctxExprMap %= Map.insert newIdx (mkConstant name levels)

    parseEA = do
      newIdx <- parseInteger <* blank
      string "#EA" >> blank
      fnIdx <- parseInteger <* blank
      argIdx <- parseInteger
      lift $ do
        use ctxExprMap >>= assertUndefined newIdx IdxExpr
        ctxExprMap <~ (uses ctxExprMap (\m -> Map.insert newIdx (mkApp (m Map.! fnIdx) (m Map.! argIdx)) m))

    parseEL = do
      newIdx <- parseInteger <* blank
      string "#EL" >> blank
      binderInfo <- parseB <* blank
      nameIdx <- parseInteger <* blank
      domainIdx <- parseInteger <* blank
      bodyIdx <- parseInteger
      lift $ do
        use ctxExprMap >>= assertUndefined newIdx IdxExpr
        name <- uses ctxNameMap (Map.! nameIdx)
        domain <- uses ctxExprMap (Map.! domainIdx)
        body <- uses ctxExprMap (Map.! bodyIdx)
        ctxExprMap %= Map.insert newIdx (mkLambda name domain body binderInfo)

    parseEP = do
      newIdx <- parseInteger <* blank
      string "#EP" >> blank
      binderInfo <- parseB <* blank
      nameIdx <- parseInteger <* blank
      domainIdx <- parseInteger <* blank
      bodyIdx <- parseInteger
      lift $ do
        use ctxExprMap >>= assertUndefined newIdx IdxExpr
        name <- uses ctxNameMap (Map.! nameIdx)
        domain <- uses ctxExprMap (Map.! domainIdx)
        body <- uses ctxExprMap (Map.! bodyIdx)
        ctxExprMap %= Map.insert newIdx (mkPi name domain body binderInfo)

    parseB :: ParserMethod BinderInfo
    parseB = try parseBD <|> try parseBI <|> try parseBS <|> parseBC
    parseBD = string "#BD" >> return BinderDefault
    parseBI = string "#BI" >> return BinderImplicit
    parseBS = string "#BS" >> return BinderStrict
    parseBC = string "#BC" >> return BinderClass

typeCheckExportFile :: String -> String -> Either String ()
typeCheckExportFile filename fileContents =
  case S.evalState (runExceptT (runParserT parseExportFile () filename fileContents))
       mkStdContext of
   Left parseErr -> Left $ show parseErr
   Right (Left kernelErr) -> Left $ show kernelErr
   Right (Right _) -> Right ()
