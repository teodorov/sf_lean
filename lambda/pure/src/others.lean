import init.data.string init.data data.buffer.parser
import .types .parsing

open lambda_types 
open lambda_types.term


def free_variables : term → list string 
| (var n) := [n]
| (application m n) := free_variables m ++ free_variables n
| (abstraction x m) := list.filter (≠ x) (free_variables m)

lemma eq1 : ∀ m : term, m = m := 
by {
    intro, induction m,
    repeat {reflexivity}
}

lemma eq2 : ∀ m n : term, m = n → n = m :=
by {
    intros,
    rw a
}
lemma eq3 : ∀ n l k : term, n = k ∧ k = l → n = l :=
by {
    intros, destruct a, intros, rw left, rw right
} 

lemma compat1 : ∀ m m' z : term, m = m' → application m z = application m' z :=
by {
    intros, rw a
}
lemma compat2 : ∀ m m' z : term, m = m' → application z m = application z m' :=
by {
   intros, rw a
}
lemma compat3 : ∀ m m' : term, ∀ x : string, m = m' → abstraction x m = abstraction x m' :=
by {
    intros, rw a
}


--have h : 1 > 0, from nat.zero_lt_succ 0,
--exists.intro 1 h

theorem fixpoint1 : ∀ F : term, ∃ X : term, application F X = X := 
by {
    intros,
    let W := abstraction "x" (application F (application (var "x") (var "x"))),
    let Z := application W W,
    --X = WW = (λx.F(xx))W = F(WW) = FX
    sorry
}

theorem fixpoint2 
    (Y : term)
    (h1: Y = 
        abstraction "f" (
            application
                ( abstraction "x" (application (var "f") ( application (var "x")  (var "x") ))) 
                ( abstraction "x" (application (var "f") ( application (var "x")  (var "x") ))))) : 
    ∀ F : term, (application F (application Y F)) = (application Y F) :=
by {
    sorry
}



def parse : string → term
| str := 
    match parser.run_string lambda_parser.LambdaParser str  with 
    | (sum.inr x) := x
    | (sum.inl _) := var "x"
    end

-- #eval list.filter (≠ 2) [1, 2, 3]

-- #eval free_variables ( (parse "(λ z x. x t) y z"))
-- #check ( (parser.run_string lambda_parser.LambdaParser "λ x. x").inr)