import .primitives

inductive static_literal 
| numeric (value: Number)
| symbol (value: Symbol)
| string (value: String)
| boolean (value: Boolean)
| character (value: Character)
| byte (value: Byte)
| array (value: list static_literal)

structure message (T : Type) : Type := 
    (selector: Symbol) (arguments: list T).

mutual inductive literal, expression, statement
with literal: Type
| static: static_literal → literal
| dynamic: list expression → literal
with expression: Type
| literal: literal → expression
| send (receiver: expression) (message: message expression) : expression
| cascade (receiver: expression) (messages: list (message expression)) : expression
| block (arguments: list Symbol) (temporaries: list Symbol) (statements: list statement) : expression
| reference (name: Symbol) : expression
with statement: Type
| exp: expression → statement
| assignment (lhs: Symbol) (rhs: expression) : statement
| return: expression → statement

structure pragma_declaration
    := (name: Symbol) (arguments: list static_literal)
inductive method_declaration
| mk (name: Symbol) (block: expression) (pragmas: list pragma_declaration)

open static_literal
open literal
open expression
open statement

#check expression.reference #"xxx"
#check assignment
#check numeric 23
#check assignment (#"xxx")  (literal (static (symbol #"xxx")))
#check assignment #"xxx" (literal (static (symbol #"xxx")))