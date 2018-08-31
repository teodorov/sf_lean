import system.io data.buffer.parser
import .types .parsing .unicode

open lambda_types lambda_parser parser

--this function transforms the environment into a wrapping lambda declaration around the target term
-- if env = ["a" : λ x. x, "b": λ y. y] and target = λ z. z x then
-- (λ x. (λ y. (λ z. z x)) y) x
def wrap_environment (environment : list (string × term)) (target: term) : term :=
match list.unzip environment with
| (names, terms) := currying (multi_abstraction names target) terms 
end

def extend_environment (environment: list (string × term)) : string × term → sum string (list (string × term))
| (name, term) := 
    if name ∈ environment.unzip.fst then 
        sum.inl $ sformat! "error: term ”{name}” is already defined"
    else
        sum.inr $ environment ++ pure (name, term)

namespace io.error
    def avoid_error {α : Type} (m : io α) : io.error → io α 
    | (io.error.other s) := (io.put_str_ln s) >> m
    | (io.error.sys n) := (io.put_str_ln $ sformat! "System error #{n}") >> m
end io.error

def help : string := "
:help                print this summary or command-specific help
:quit                exit the interpreter
:env                 show variables in the scope
:show_depth          show current recursion depth
:depth [nat]         set recursion depth
:show_import_depth   show current import depth
:import_depth [nat]  set import depth
:clear_env           clear environment
:load [filename]     load file “filename”
let name := body     creates a new variable “name” with value “body”
<lambda term>        evaluate term lambda term"

structure repl_configuration := 
(environment: list (string × term))
(recursion_depth: nat)
(import_depth: nat)

def read_from_file : nat → repl_configuration → string → io repl_configuration
| 0 conf _ := pure conf
| (n+1) conf filename := do
    filehandle ← io.mk_file_handle filename io.mode.read,
    new_conf ← io.iterate conf
    (λ (conf : repl_configuration),
      do eof ← io.fs.is_eof filehandle,
        if eof then pure none
        else do
          line ← (flip option.get_or_else "") <$>
                 unicode.utf8_to_string <$>
                 io.fs.get_line filehandle,
          let file_eval := eval conf.recursion_depth ∘ wrap_environment conf.environment,
          match run_string CommandParser line with
            | (sum.inr $ repl_command.term t) := do
              let (evaluated, info) := file_eval t,
              io.put_str_ln $ sformat! "{line} ⇒ {evaluated} ({info})",
              pure conf
            | (sum.inr $ repl_command.bind name t) :=
              match extend_environment conf.environment (name, (file_eval t).2) with
              | sum.inr new_env := pure $ some { conf with environment := new_env }
              | sum.inl error_msg := io.fail error_msg
              end
            | (sum.inr $ repl_command.load filename) :=
              some <$> (read_from_file n conf filename)
            | (sum.inl er) := do io.put_str_ln er, pure none
            | _ := pure $ some conf
          end),
    io.fs.close filehandle,
    pure new_conf

def print_env (conf: repl_configuration): io unit := do
    list.foldl (>>) (pure ()) $
      list.map (λ (var : string × term),
        io.put_str_ln $ sformat! "{var.1} := {var.2}")
        conf.environment

def loop : repl_configuration → io (option repl_configuration)
| conf := 
    let 
        repl_eval := eval conf.recursion_depth ∘ wrap_environment conf.environment 
    in do
        io.put_str "λ> ",
        line ← io.get_line,
        match run_string CommandParser line with
        | (sum.inr repl_command.quit) := pure none
        | (sum.inr repl_command.help) := io.put_str_ln help >> pure conf
        | (sum.inr repl_command.env) := print_env conf >> pure conf
        | (sum.inr repl_command.clear_env) := pure $ some {conf with environment := []}
        | (sum.inr $ repl_command.depth depth) := pure $ some {conf with recursion_depth := depth}
        | (sum.inr repl_command.show_depth) := (io.put_str_ln $ to_string conf.recursion_depth) >> pure conf
        | (sum.inr $ repl_command.import_depth depth) := pure $ some {conf with import_depth := depth}
        | (sum.inr repl_command.show_import_depth) := (io.put_str_ln $ to_string conf.import_depth) >> pure conf
        | (sum.inr $ repl_command.bind name term) := 
            match extend_environment conf.environment (name, (repl_eval term).2) with
            | sum.inr new_env := pure $ some {conf with environment := new_env}
            | sum.inl error_msg := io.put_str_ln error_msg >> pure (some conf)
            end
        | (sum.inr $ repl_command.term term) := 
            let result := repl_eval term in
            do io.put_str_ln $ sformat! "{result.1}\n-- {result.2}", pure conf
        | (sum.inr $ repl_command.load name) := some <$> read_from_file conf.import_depth conf name
        | (sum.inl er) := do io.put_str_ln er, pure conf
        | _ := pure conf
        end

open lambda_types.term
def basic_environment : list (string × term) :=
[ ("I", abstraction "x" (var "x")),
  ("K", multi_abstraction ["x", "y"] (var "x")),
  ("S", multi_abstraction ["f", "g", "x"]
    (application 
        (application (var "f") (var "x"))
        (application (var "g") (var "x"))))
]

def initial_configuration : repl_configuration :=
    {import_depth := 1000, recursion_depth := 1000, environment := basic_environment}

def main : io unit := do
    args ← io.cmdline_args,
    conf ← pure initial_configuration,
    io.put_str_ln "Type ”:help” for help.",
    io.iterate conf 
        (λ (c : repl_configuration),
            io.catch (loop c) (io.error.avoid_error $ pure c)) >> pure ()