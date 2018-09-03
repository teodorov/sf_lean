namespace lambda_types

inductive term : Type
| var : string → term
| abstraction : string → term → term
| application : term → term → term
open term

def multi_abstraction (names: list string) (body: term): term := 
    list.foldr abstraction body names

def currying (body: term) (values: list term): term :=
    list.foldl application body values

def term_to_string : term → string
| (var n) := sformat! "{n}"
| (abstraction name term) := sformat! "λ{name}. {term_to_string term}"
| (application t₁ t₂) := sformat! "({term_to_string t₁}) {term_to_string t₂}"

instance term_has_to_string : has_to_string term := ⟨ term_to_string ⟩ 
instance term_has_repr : has_repr term := ⟨ term_to_string ⟩ 

def substitution : string → term → term → term 
| x newVal (var y) := 
    if x ≠ y then var y
    else newVal
| x newVal (abstraction y body) := 
    if x ≠ y then abstraction y (substitution x newVal body )
    else abstraction y body
| x newVal (application t₁ t₂) :=
    application (substitution x newVal t₁) (substitution x newVal t₂)

inductive result
| overflow
| normal

def result_to_string : result → string
| result.overflow := "stack overflow (max recursion depth reached)"
| result.normal := "normal form"
instance result_has_to_string : has_to_string result := ⟨ result_to_string ⟩
instance result_has_repr : has_repr result := ⟨ result_to_string ⟩ 

def eval : ∀ (max_depth : ℕ), term → result × term
| 0 t := (result.overflow, t)
| _ (var n) := (result.normal, var n)
| _ (abstraction n t) := (result.normal, abstraction n t)
| (n+1) (application t₁ t₂) :=
    match eval n t₁ with 
    | (_, (abstraction x body)) := eval n (substitution x t₂ body)
    | (r, t) := (r, (application t t₂))
    end

inductive repl_command 
| term: term → repl_command
| quit
| help
| env
| show_depth
| clear_env
| nothing
| show_import_depth
| load: string → repl_command
| depth: nat → repl_command
| import_depth: nat → repl_command
| bind: string → term → repl_command

def repl_command_to_string : repl_command → string
| (repl_command.term term) := sformat! "term {term_to_string term}"
| (repl_command.quit) := sformat! "quit"
| (repl_command.help) := sformat! "help"
| (repl_command.env) := sformat! "env"
| (repl_command.show_depth) := sformat! "show_depth"
| (repl_command.clear_env) := sformat! "clear_env"
| (repl_command.nothing) := sformat! "nothing"
| (repl_command.show_import_depth) := sformat! "show_import_depth"
| (repl_command.load name) := sformat! "load {name}"
| (repl_command.depth n) := sformat! "depth {n}"
| (repl_command.import_depth n) := sformat! "import_depth {n}"
| (repl_command.bind name term) := sformat! "bind [{name} := {term_to_string term}]"


instance repl_command_has_to_string : has_to_string repl_command := ⟨ repl_command_to_string ⟩
instance repl_command_has_repr : has_repr repl_command := ⟨ repl_command_to_string ⟩ 


--#eval multi_abstraction ["a", "b"] (var "a")
--#eval currying (var "f") [(var "x"), (var "y")]

end lambda_types