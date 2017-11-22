structure position :=
(line : ℕ) (column : ℕ)

structure range :=
(left : position) (right : position)

structure location :=
(file : string) (range : range)

inductive origin
| file (loc : location)
| synthetic

meta inductive syntax
| num (n : ℕ)
| name (n : name)
| string (s : string)
| quote (e : expr)
| node (o : origin) (kind : name) (children : list syntax)

/-
match x with
| list.cons x xs := x
| _ := 42
end
-/
#eval
let o (l1 c1 l2 c2 : ℕ) := origin.file ⟨"example1.lean", ⟨l1,c1⟩, ⟨l2,c2⟩⟩ in
syntax.node (o 1 0 4 3) `match [
    syntax.node (o 1 6 1 7) `ident [syntax.name `x],
    syntax.node (o 2 2 2 16) `app [
        syntax.node (o 2 2 2 11) `ident [syntax.name `list.cons],
        syntax.node (o 2 12 2 13) `ident [syntax.name `x],
        syntax.node (o 2 14 2 16) `ident [syntax.name `xs]
    ],
    syntax.node (o 2 20 2 21) `ident [syntax.name `x],
    syntax.node (o 3 2 3 3) `placeholder [],
    syntax.node (o 3 7 3 9) `num [syntax.num 42]
]

/-
λ x, x + 2
-/
#eval
let o (l1 c1 l2 c2 : ℕ) := origin.file ⟨"example2.lean", ⟨l1,c1⟩, ⟨l2,c2⟩⟩ in
syntax.node (o 1 0 1 10) `lambda [
    syntax.name `x,
    syntax.name `default,
    syntax.node origin.synthetic `placeholder [],
    syntax.node (o 1 5 1 10) `app [
        syntax.node (o 1 7 1 8) `ident [syntax.name `+],
        syntax.node (o 1 5 1 6) `ident [syntax.name `x],
        syntax.node (o 1 9 1 10) `num [syntax.num 2]
    ]
]