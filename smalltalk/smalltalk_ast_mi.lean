import .primitives1

inductive static_literal 
| nil
| numeric (value: Number)
| symbol (value: Symbol)
| string (value: String)
| boolean (value: Boolean)
| character (value: Character)
| byte_array (value: list Byte)
| array (value: list static_literal)

structure message (T : Type) : Type := 
    (selector: Symbol) (arguments: list T).

mutual inductive literal, expression, statement
with literal: Type
| static: static_literal → literal
| dynamic: list expression → literal
| block (arguments: list Symbol) (temporaries: list Symbol) (statements: list statement) : literal
with expression: Type
| literal: literal → expression
| send (receiver: expression) (message: message expression) : expression
| cascade (receiver: expression) (messages: list (message expression)) : expression
| reference (name: Symbol) : expression
| self
| super
| thisContext
with statement: Type
| exp: expression → statement
| assignment (lhs: Symbol) (rhs: expression) : statement
| return: expression → statement

structure pragma_declaration
    := (name: Symbol) (arguments: list static_literal)
inductive method_declaration
| mk (name: Symbol) (block: expression) (pragmas: list pragma_declaration)
.