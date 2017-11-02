import .primitives

section Smalltalk_AST
structure ASTNode := new 
structure Decl extends ASTNode := (name: Symbol)
structure VariableDecl extends Decl := new
structure Stmt extends ASTNode := new
structure Expr extends Stmt := new
structure Lit extends Expr := new

structure StaticLit extends Lit := new
structure NumericLit extends StaticLit 
    := (value: Number)
structure SymbolLit extends StaticLit 
    := (value: Symbol)
structure StringLit extends StaticLit 
    := (value: String)
structure BooleanLit extends StaticLit 
    := (value: Boolean)
structure CharacterLit extends StaticLit 
    :=  (value: Character)
structure ByteArrayLit extends StaticLit 
    := (value: list Byte)
structure StaticArrayLit extends StaticLit 
    := (value: list StaticLit)

structure DynamicArrayLit extends Lit 
    := (value: list Expr)

structure MessageExpr extends Expr 
    := (receiver: Expr) (selector: Symbol) (arguments: list Expr)
structure CascadeExpr extends Expr 
    := (messages: list MessageExpr)
structure BlockExpr extends Expr 
    := (arguments: list VariableDecl) (temporaries: list VariableDecl) (Stmts: list Stmt)
structure ReferenceExpr extends Expr 
    := (name: Symbol)

structure AssignmentStmt extends Stmt 
    := (target: ReferenceExpr) (value: Expr)
structure ReturnStmt extends Stmt 
    := (value: Expr)

structure PragmaDecl extends Decl 
    := (arguments: list StaticLit)
structure MethodDecl extends Decl 
    := (block: BlockExpr) (pragmas: list PragmaDecl)
end Smalltalk_AST


section Smalltalk_AST_Coercions
instance NumericLit_to_StaticLit_coe : has_coe (NumericLit) (StaticLit) := ⟨ NumericLit.to_StaticLit ⟩ 
instance SymbolLit_to_StaticLit_coe : has_coe (SymbolLit) (StaticLit) := ⟨ SymbolLit.to_StaticLit ⟩ 
instance StringLit_to_StaticLit_coe : has_coe (StringLit) (StaticLit) := ⟨ StringLit.to_StaticLit ⟩ 
instance BooleanLit_to_StaticLit_coe : has_coe (BooleanLit) (StaticLit) := ⟨ BooleanLit.to_StaticLit ⟩ 
instance CharacterLit_to_StaticLit_coe : has_coe (CharacterLit) (StaticLit) := ⟨ CharacterLit.to_StaticLit ⟩
instance ByteArrayLit_to_StaticLit_coe : has_coe (ByteArrayLit) (StaticLit) := ⟨ ByteArrayLit.to_StaticLit ⟩
instance StaticArrayLit_to_StaticLit_coe : has_coe (StaticArrayLit) (StaticLit) := ⟨ StaticArrayLit.to_StaticLit ⟩

instance StaticLit_to_Lit_coe : has_coe (StaticLit) (Lit) := ⟨ StaticLit.to_Lit ⟩
instance DynamicArrayLit_to_Lit_coe : has_coe (DynamicArrayLit) (Lit) := ⟨ DynamicArrayLit.to_Lit ⟩

instance Lit_to_Expr_coe : has_coe (Lit) (Expr) := ⟨ Lit.to_Expr ⟩
instance Expr_to_Stmt_coe : has_coe (Expr) (Stmt) := ⟨ Expr.to_Stmt ⟩ 

instance MessageExpr_to_Expr_coe : has_coe (MessageExpr) (Expr) := ⟨ MessageExpr.to_Expr ⟩
instance CascadeExpr_to_Expr_coe : has_coe (CascadeExpr) (Expr) := ⟨ CascadeExpr.to_Expr ⟩ 
instance BlockExpr_to_Expr_coe : has_coe (BlockExpr) (Expr) := ⟨ BlockExpr.to_Expr ⟩ 
instance ReferenceExpr_to_Expr_coe : has_coe (ReferenceExpr) (Expr) := ⟨ ReferenceExpr.to_Expr ⟩ 

instance AssignmentStmt_to_Stmt_coe : has_coe (AssignmentStmt) (Stmt) := ⟨ AssignmentStmt.to_Stmt ⟩ 
instance ReturnStmt_to_Stmt_coe : has_coe (ReturnStmt) (Stmt) := ⟨ ReturnStmt.to_Stmt ⟩ 

instance VariableDecl_to_Decl_coe : has_coe (VariableDecl) (Decl) := ⟨ VariableDecl.to_Decl ⟩
instance PragmaDecl_to_Decl_coe : has_coe (PragmaDecl) (Decl) := ⟨ PragmaDecl.to_Decl ⟩
instance MethodDecl_to_Decl_coe : has_coe (MethodDecl) (Decl) := ⟨ MethodDecl.to_Decl ⟩ 

instance Decl_to_ASTNode_coe : has_coe (Decl) (ASTNode) := ⟨ Decl.to_ASTNode ⟩
instance Stmt_to_ASTNode_coe : has_coe (Stmt) (ASTNode) := ⟨ Stmt.to_ASTNode ⟩ 
end Smalltalk_AST_Coercions

section Smalltalk_AST_Examples
#check {NumericLit . value := 23}
#check {SymbolLit . value := #"abcd"}
#check {StringLit . value := "abcd"}
#check {BooleanLit . value := true}
#check {BooleanLit . value := false}
#check {CharacterLit . value := $'c' }
#check {ByteArrayLit . value := [1, 2, 300]}
def arr1 := {StaticArrayLit . value := [
            ↑ {NumericLit . value := 23}, 
            ↑ {SymbolLit . value := #"abcd"}]}

#check {StaticArrayLit . value := [
            ↑ {NumericLit . value := 23}, 
            ↑ {SymbolLit . value := #"abcd"}]}
#check {StaticArrayLit . value := [
            ↑ {NumericLit . value := 23}, 
            ↑ {SymbolLit . value := #"abcd"}, 
            ↑ {StringLit . value := "abcd"},
            ↑ {BooleanLit . value := true},
            ↑ {CharacterLit . value := $'c' },
            ↑ {ByteArrayLit . value := [1, 2, 300]},
            ↑ arr1]}

#check {DynamicArrayLit . value := [ ↑ {NumericLit . value := 23} ]}
#check { MessageExpr . receiver := ↑ {NumericLit . value := 23}, selector := #"abcd" , arguments := []}

#check { MethodDecl . name := #"abc", block := { arguments := [], temporaries:=[],Stmts:=[] }, pragmas:=[]}
end Smalltalk_AST_Examples