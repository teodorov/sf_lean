import data.buffer.parser
import .types
open parser lambda_types

namespace lambda_parser

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

def LetParser : parser (string × term) := do
    str "let", many1 WS,
    name ← Word, many1 WS,
    str ":=", many WS,
    body ← LambdaParser,
    pure (name, body)

def Numeral : parser char :=
sat $ λ c, list.any "0123456789".to_list (= c)
def NumberParser := many_char1 Numeral

def CommandLineParser : parser repl_command :=
str ":quit" >> pure repl_command.quit <|>
str ":help" >> pure repl_command.help <|>
str ":env" >> pure repl_command.env <|>
str ":depth" >> WS >> NumberParser >>= (pure ∘ repl_command.depth ∘ string.to_nat) <|>
str ":import_depth" >> WS >> NumberParser >>= (pure ∘ repl_command.import_depth ∘ string.to_nat) <|>
str ":show_depth" >> pure repl_command.show_depth <|>
str ":show_import_depth" >> pure repl_command.show_import_depth <|>
str ":clear_env" >> pure repl_command.clear_env <|>
str ":load" >> WS >> many_char1 (sat (λ c, list.all (whitespaces) (≠ c))) >>= pure ∘ repl_command.load <|>
LetParser >>= (pure ∘ function.uncurry repl_command.bind) <|>
LambdaParser >>= (pure ∘ repl_command.term) <|>
many WS >> pure repl_command.nothing

def CommandParser: parser repl_command := do
    cmd ← CommandLineParser,
    optional (str "--" >> optional WS >> many (sat (λ _, tt))),
    optional $ many WS,
    pure cmd

#eval run CommandLineParser "let pair := x".to_char_buffer

end lambda_parser