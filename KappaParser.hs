module KappaParser where

import Prelude hiding (init)
import Control.Applicative ((<*))
-- Parsec
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token
import Text.Parsec.Language
import Text.Parsec.Error

-- Types
type SiteName = String
type InternalState = String
type BondLabel = Int
data BindingState = Free | SemiLink | Bound BondLabel | Unspecified
  deriving Show
data Site = Site SiteName InternalState BindingState
  deriving Show

type AgentName = String
type Interface = [Site]
data Agent = Agent AgentName Interface
  deriving Show

type Expr = [Agent]

-- type AE = Sum AE AE | Minus AE AE | Mult AE AE | Div AE AE | Mod AE AE | Pow AE AE | Log AE | Ln AE | Sqrt AE | Exp AE | Sin AE | Cos AE | Tan AE | Abs AE | Var String | Number Double | Inf deriving Show
type RuleName = String
type Rate = Double -- AE
data Rule = Rule RuleName Expr Expr Rate
  deriving Show

-- Language definition
def = emptyDef{ commentLine = "#"
              , nestedComments = True
              , identStart = letter
              , identLetter = alphaNum
              , reservedNames = ["->", "@"]
              }

TokenParser{ parens = m_parens
           , decimal = m_decimal
           , float = m_float
           , colon = m_colon
           , commaSep = m_commaSep
           , commaSep1 = m_commaSep1
           , symbol = m_symbol
           , reserved = m_reserved
           , identifier = m_identifier
           , whiteSpace = m_whiteSpace } = makeTokenParser def

-- Partial parsers
agent :: Parser Agent
agent = do name <- agentName <?> "agent"
           intf <- m_parens interface <?> "interface"
           return $ Agent name intf

agentName :: Parser String
agentName = m_identifier

interface :: Parser Interface
interface = m_commaSep1 site

site :: Parser Site
site = do siteName <- m_identifier <?> "site name"
          internalState <- (m_symbol "~" >> m_identifier) <|> return ""
          bindingState <- (m_symbol "!" >> (do bondLabel <- m_decimal
                                               return . Bound . fromIntegral $ bondLabel
                                            <|>
                                            do m_symbol "_"
                                               return SemiLink))
                          <|> (m_symbol "?" >> return Unspecified)
                          <|> return Free
          return $ Site siteName internalState bindingState

expr :: Parser Expr
expr = m_commaSep agent <?> "expression"

rule :: Parser Rule
rule = do char '\'' -- FIXME rule labels should be optional
          name <- many1 $ noneOf "'"
          m_symbol "'"
          lhs <- expr
          m_reserved "->" <?> "arrow"
          rhs <- expr
          m_reserved "@"
          rate <- m_float
          return $ Rule name lhs rhs rate

-- Complete parsers
agentParser = m_whiteSpace >> agent <* eof
exprParser = m_whiteSpace >> expr <* eof
ruleParser = m_whiteSpace >> rule <* eof

-- Kappa file
-- Types
data SigSite = SigSite SiteName [InternalState]
  deriving Show
type SigIntf = [SigSite]
data Sig = Sig AgentName SigIntf
  deriving Show

type VarName = String
data Decl = SigDecl Sig | Init Int Expr | Obs VarName Expr | RuleDecl Rule
  deriving Show

type Model = [Decl]

-- Partial parsers
sig :: Parser Sig
sig = do name <- agentName <?> "agent signature"
         intf <- m_parens sigIntf <?> "signature interface"
         return $ Sig name intf

sigIntf :: Parser SigIntf
sigIntf = m_commaSep1 sigSite

sigSite :: Parser SigSite
sigSite = do siteName <- m_identifier <?> "site name"
             internalStates <- many (m_symbol "~" >> m_identifier)
             return $ SigSite siteName internalStates

init :: Parser Decl
init = do n <- m_decimal
          m_whiteSpace
          e <- expr
          return $ Init (fromIntegral n) e

obs :: Parser Decl
obs = do char '\''
         id <- m_identifier
         m_symbol "'"
         e <- expr
         return $ Obs id e

-- Complete parsers
kappaFileParser :: Parser Model
kappaFileParser = m_whiteSpace >> many kappaFileLine <* eof

kappaFileLine :: Parser Decl
kappaFileLine = (char '%' >> ((string "agent" >> m_colon >> sig >>= (return . SigDecl))
                              <|> (string "init" >> m_colon >> init)
                              <|> (string "obs" >> m_colon >> obs)))
                <|> do r <- rule
                       return $ RuleDecl r

-- Helper functions
simpleParse :: String -> Parser a -> a
simpleParse s p = case parse p "" s of
                    Left e -> error $ show e -- ParseError
                    Right result -> result

parseExpr :: String -> Expr
parseExpr exprStr = simpleParse exprStr expr

parseRule :: String -> Rule
parseRule ruleStr = simpleParse ruleStr rule

parseKappaFile :: String -> [Decl]
parseKappaFile kfStr = simpleParse kfStr kappaFileParser

