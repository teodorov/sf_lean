namespace lambda_types

inductive Constant 
| int : int → Constant
| nat : nat → Constant
| bool : bool → Constant

inductive AST
| var : string → AST
| literal : Constant → AST
| primitive : string → AST → AST → AST
| abstraction : string → AST → AST
| application : AST → AST → AST
| conditional : AST → AST → AST → AST
| letrec (id : string) (x : AST) : AST
end lambda_types