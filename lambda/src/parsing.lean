import data.buffer.parser
import .types
open parser lambda_types

namespace parsing

def whitespaces := " \t\n\x0d".to_list
def reserved_chars := [' ', '.', 'λ', '(', ')']
def CHAR : parser char :=
    sat (λ c, list.all (reserved_chars ++ whitespaces) (≠ c))

def LF := ch $ char.of_nat 10
def CR := ch $ char.of_nat 13
def NL := CR >> LF <|> LF <|> CR
def WS : parser unit :=
    decorate_error "<whitespace>" $ many' $ one_of' whitespaces

def Word : parser string := many_char1 CHAR

def tok (s: string) := str s >> WS

def VarParser : parser term := do
    name ← Word,
    pure $ term.var name

def AbstractionParser (termParser : parser term) : parser term := do
    ch 'λ', many WS,
    names ← sep_by1 WS Word,
    ch '.', many WS,
    body ← termParser,
    pure $ multi_abstraction names body

def ApplicationParser (termParser : parser term) : parser term := do
    function ← termParser, many WS,
    arguments ← sep_by WS termParser,
    pure $ currying function arguments

def ParenthesisParser (termParser : parser term) : parser term := do
    termParser <|> (ch '(' >> termParser <* ch ')')

def LambdaParserCore (termParser : parser term) : parser term := 
    let
    term := AbstractionParser (ParenthesisParser termParser) 
        <|> ApplicationParser (ParenthesisParser termParser) 
        <|> VarParser
    in ParenthesisParser term

def LambdaParser := fix LambdaParserCore

end parsing