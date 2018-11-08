namespace sf_basics

inductive day : Type 
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

inductive day1 : Type 
| monday 
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.
#check day1.monday

def next_weekday : day → day 
| day.monday := day.tuesday
| day.tuesday := day.wednesday
| day.wednesday := day.thursday
| day.thursday := day.friday
| day.friday := day.saturday
| day.saturday := day.sunday
| day.sunday := day.monday.

#reduce next_weekday day.friday
#reduce next_weekday day.saturday

example : (next_weekday (next_weekday day.saturday)) = day.monday
        := by {reflexivity}

inductive bool : Type 
| true 
| false

namespace bool
def negb : bool → bool 
| true := false
| false := true.

def andb : bool → bool → bool
| true b₂ := b₂ 
| false _ := false.

def orb : bool → bool → bool
| true _ := true
| false b₂ := b₂.

example : (orb true false) = true := 
    by { reflexivity }

example : (orb false false) = false :=
    by { reflexivity }

example : (orb false true) = true := 
    by { reflexivity }

example : (orb true true) = true :=
    by { reflexivity }

notation x `&&` y := (andb x y)
notation x `||` y := (orb x y)

example : false || false || true = true :=
    by { reflexivity }

def nandb (x y: bool):  bool := negb (x && y)

example : (nandb true false) = true :=
    by { reflexivity }
example : (nandb false false) = true :=
    by { reflexivity }
example : (nandb false true) = true :=
    by { reflexivity }
example : (nandb true true) = false :=
    by { reflexivity }

def andb3 (x y z : bool) : bool := x && y && z

example : (andb3 true true true) = true :=
    by { reflexivity }
example : (andb3 false true true) = false :=
    by { reflexivity }
example : (andb3 true false true) = false :=
    by { reflexivity }
example : (andb3 true true false) = false :=
    by { reflexivity }.

#check true
#check (negb true)
#check negb
#check true
end bool
namespace compound
open sf_basics.bool
--Compound types
inductive rgb : Type 
| red : rgb 
| green : rgb
| blue : rgb.

inductive color : Type 
| black : color
| white : color
| primary : rgb → color.

def monochrome (c:color) : color → bool 
| color.black := true
| color.white := true
| (color.primary p) := false.

def isred : color → bool
| color.black := false
| color.white := false
| (color.primary rgb.red) := true
| (color.primary _) := false.
end compound

inductive nat : Type
| O
| S : nat → nat


namespace nat
open sf_basics.bool
#check O

def pred : nat → nat
| O := O
| (S n') := n'

@[simp] def succn : nat → nat
| O := S O
| (S n') := S (S n')

#reduce pred (S (S (S (S O))))

def minustwo : nat → nat 
| O := O
| (S O) := O
| (S (S n')) := n'

#reduce minustwo (S (S (S (S O))))

def evenb : nat → bool 
| O := true
| (S O) := false
| (S (S n')) := evenb n'

#reduce evenb (S (S (S (S O))))
#reduce evenb (S (S (S O)))

def oddb (n:nat) : bool := negb (evenb n)

example : oddb (S O) = true := by {reflexivity}
example : oddb (S (S (S (S O)))) = false := by {reflexivity}

def plus : nat → nat → nat
| O m := m
| (S n') m := S (plus n' m)

#reduce plus (S (S (S O))) (S (S O)) 

def mult : nat → nat → nat
| O _ := O
| (S n') m := plus m (mult n' m)

@[simp] def n_to_nat : ℕ → nat 
| 0 := O
| (nat.succ n') := S (n_to_nat n')

@[simp] def nat_to_n : nat → ℕ 
| O := 0
| (S n') := nat.succ (nat_to_n n')

#reduce nat_to_n (S (S (S O)))

lemma n_to_nat_to_n : ∀ x : ℕ, nat_to_n (n_to_nat x) = x :=
by {intros, induction x; simp [*, n_to_nat, nat_to_n]}

example : (mult (S (S (S O))) (S (S (S O)))) = n_to_nat 9 :=
    by { reflexivity }

def minus : nat → nat → nat 
| O _ := O
| (S n) O := n
| (S n') (S m') := minus n' m'

def exp : nat → nat → nat
| _ O := S O
| base (S p) := mult base (exp base p)

def factorial : nat → nat 
| O := (S O)
| (S n) := mult (S n) (factorial n)

example : factorial (n_to_nat 3) = n_to_nat 6 :=
    by {reflexivity}

example : factorial (n_to_nat 5) = n_to_nat 120 :=
    by {reflexivity}

example : factorial (n_to_nat 5) = mult (n_to_nat 10) (n_to_nat 12) :=
    by {reflexivity}

notation x `+` y := plus x y
notation x `-` y := minus x y
notation x `*` y := mult x y
notation x `!!` := factorial x

example : factorial (n_to_nat 5) = (n_to_nat 10) * (n_to_nat 12) :=
    by {reflexivity}

example : (n_to_nat 5) !! = (n_to_nat 10) * (n_to_nat 12) :=
    by {reflexivity}

def beq_nat : nat → nat → bool
| O O := true
| O m := false
| m O := false
| (S n') (S m') := beq_nat n' m'

def leb : nat → nat → bool
| O _ := true
| _ O := false
| (S n') (S m') := leb n' m'

example : leb (n_to_nat 2) (n_to_nat 2) = true :=
    by {reflexivity}

example : leb (n_to_nat 2) (n_to_nat 4) = true :=
    by {reflexivity}

example : leb (n_to_nat 4) (n_to_nat 2) = false :=
    by {reflexivity}

def blt_nat (n m : nat) : bool := (leb n m) && negb (beq_nat n m)

example : blt_nat (n_to_nat 2) (n_to_nat 2) = false :=
    by {reflexivity}

example : blt_nat (n_to_nat 2) (n_to_nat 4) = true :=
    by {reflexivity}

example : blt_nat (n_to_nat 4) (n_to_nat 2) = false :=
    by {reflexivity}

theorem plus_O_n : ∀ n : nat, O + n = n :=
by {intros, simp [plus]}

namespace h1
theorem plus_O_n : ∀ n : nat, O + n = n :=
by {intros, reflexivity}
end h1

theorem plus_1_n : ∀ n : nat, (S O) + n = S n := 
by {intros, simp [plus]}

theorem mult_O_n : ∀ n : nat, O * n = O := 
by {intros, simp [mult]}

theorem plus_id_example : ∀ n m : nat,
    n = m → n+n =m+m :=
by {
    intros n m h, 
    rw h
}

theorem plus_id_example1 : ∀ n m : nat,
    n = m → n+n =m+m :=
by {intros, simp [*]}

theorem plus_id_exercise : ∀ n m o : nat,
    n = m → m=o → n + m = m + o
:= by {
    intros n m o h₁ h₂,
    rw h₁, rw h₂,
}

theorem plus_id_exercise1 : ∀ n m o : nat,
    n = m → m=o → n + m = m + o
:= by { intros, simp [*] }

theorem mult_O_plus : ∀ n m : nat,
    (O + n) * m = n * m
:= by {intros, rw plus_O_n}

theorem mult_O_plus1 : ∀ n m : nat,
    (O + n) * m = n * m
:= by {intros, simp [plus_O_n]}

theorem mult_S_1 : forall n m : nat,
    m = S n → m * ((S O) + n) = m * m
:= by { intros, rw plus_1_n, rw ← a }


theorem mult_S_11 : forall n m : nat,
    m = S n → m * ((S O) + n) = m * m
:= by { intros, rw plus_1_n, rw a}

theorem mult_S_12 : forall n m : nat,
    m = S n → m * ((S O) + n) = m * m
:= by { intros, simp [*, plus_1_n]}

theorem mult_S_13 : forall n m : nat,
    m = S n → m * ((S O) + n) = m * m
:= by { intros, simp *, reflexivity}

theorem plus_1_neg_O : ∀ n : nat,
    beq_nat (n + (S O)) O = false
:= by {
    intros, 
    cases n, 
        { reflexivity },
        { reflexivity }
}

theorem plus_1_neg_O1 : ∀ n : nat,
    beq_nat (n + (S O)) O = false
:= by {intros, cases n; reflexivity}

theorem negb_involutive : ∀ b : bool,
    negb (negb b) = b
:= by { intros, cases b, reflexivity, reflexivity }

theorem negb_involutive1 : ∀ b : bool,
    negb (negb b) = b
:= by { intros, cases b; reflexivity}

theorem andb_commutative : ∀ b c, andb b c = andb c b
:= by {
    intros, 
    cases b,
        cases c,
            reflexivity,
            reflexivity,
        cases c,
            reflexivity,
            reflexivity
}

theorem andb_commutative1 : ∀ b c, andb b c = andb c b
:= by {
    intros, 
    cases b,
    { cases c,
        { reflexivity },
        { reflexivity }},
    { cases c,
        { reflexivity },
        { reflexivity }}}

theorem andb_commutative2 : ∀ b c, andb b c = andb c b
:= by {intros, cases b; cases c; reflexivity}

theorem andb3_exchange : ∀ b c d,
    andb (andb b c) d = andb (andb b d) c
:= by {
    intros, cases b; cases c; cases d; reflexivity
}

theorem andb3_exchange1 : ∀ b c d,
    andb (andb b c) d = andb (andb b d) c
:= by {
    intros,
    destruct b,
    {   intros, rw a,
        destruct c,
        {
            intros, rw a_1,
            destruct d,
            { intros, rw a_2 },
            { intros, rw a_2, reflexivity }
        },
        {
            intros, rw a_1,
            destruct d,
            { intros, rw a_2, reflexivity },
            { intros, rw a_2 }
        }
    },
    {   intros, rw a,
        destruct c,
        {
            intros, rw a_1,
            destruct d,
            { intros, rw a_2 },
            { intros, rw a_2, reflexivity }
        },
        {
            intros, rw a_1,
            destruct d,
            { intros, rw a_2, reflexivity },
            { intros, rw a_2 }
        }
    }
}

theorem andb3_exchange2 : ∀ b c d,
    andb (andb b c) d = andb (andb b d) c
:=  by {
    intros, destruct b; { 
        intros, rw a, destruct c; { 
            intros, rw a_1, destruct d; {
                intros, { rw a_2, reflexivity } <|> rw a_2 } } } 
}

theorem andb3_exchange3 : ∀ b c d,
    andb (andb b c) d = andb (andb b d) c
:=  by {
    intros, destruct b; { 
        intros, rw a, destruct c; { 
            intros, rw a_1, destruct d; {
                intros, rw a_2, try { reflexivity } } } } 
}

theorem andb_true_elim2 : ∀ b c : bool,
    andb b c = true → c = true 
:= by {
    intros b c,
    cases b,
        cases c, 
            { intro, reflexivity },
            { simp [andb] },
        cases c,
            { simp [andb] },
            { simp [andb] }
}

theorem andb_true_elim21 : ∀ b c : bool,
    andb b c = true → c = true 
:= by {
    intros b c, cases b; cases c; {simp [andb], try {intro, assumption}}
}

theorem zero_nbeq_plus_1 : ∀ n : nat,
    beq_nat O ( n + (S O)) = false
:= by { intros, cases n; reflexivity }

def plus' : nat → nat → nat 
| n O := n
| n (S m') := S (plus' n m')

-- def lim : ℕ → ℕ 
-- | 5 := 5
-- | n := if n > 5 then lim n-1 else lim n+1

theorem identity_fn_applied_twice :
    ∀ f : bool → bool, (∀ x : bool, f x = x) → ∀ b : bool, f (f b) = b
:= by { intros, cases b; simp [*] }

theorem identity_fn_applied_twice1 :
    ∀ f : bool → bool, (∀ x : bool, f x = x) → ∀ b : bool, f (f b) = b
:= by { intros, rw a, rw a }

theorem identity_fn_applied_twice2 :
    ∀ f : bool → bool, (∀ x : bool, f x = x) → ∀ b : bool, f (f b) = b
:= by { intros, repeat {rw a} }

theorem negation_fn_applied_twice :
    ∀ f : bool → bool, (∀ x : bool, f x = negb x) → ∀ b : bool, f (f b) = b
:= by { intros, repeat { rw a }, simp [negb_involutive] }

theorem negation_fn_applied_twice1 :
    ∀ f : bool → bool, (∀ x : bool, f x = negb x) → ∀ b : bool, f (f b) = b
:= by { intros, repeat { rw a }, apply negb_involutive }

theorem andb_eq_orb :
    ∀ ( b c : bool), (andb b c = orb b c) → b = c
:= by { intros b c, cases b; cases c; simp [andb, orb]; intro; rw a }



end nat

inductive bin : Type 
| zero
| twice : bin → bin
| twicep1 : bin → bin

namespace bin
open sf_basics.nat
@[simp] def incr : bin → bin
| zero          := twicep1 zero
| (twice n)     := twicep1 n
| (twicep1 n)   := twice (incr n)

@[simp] def bin_to_nat : bin → nat
| zero          := O
| (twice n)     := (S (S O)) * (bin_to_nat n)
| (twicep1 n)   := ((S (S O)) * (bin_to_nat n)) + (S O)

def one     : bin := (twicep1 zero)
def two     : bin := (twice (twicep1 zero))
def three   : bin := (twicep1 (twicep1 zero))
def four    : bin := (twice (twice (twicep1 zero)))

example : bin_to_nat zero   = O                 := by { reflexivity }
example : bin_to_nat one    = S O               := by { reflexivity }
example : bin_to_nat two    = S (S O)           := by { reflexivity }
example : bin_to_nat three  = S (S (S O))       := by { reflexivity }
example : bin_to_nat four   = S( S (S (S O)))   := by { reflexivity }

example : bin_to_nat(incr zero) = S O                   := by {reflexivity}
example : bin_to_nat(incr one)  = S (S O)               := by {reflexivity}
example : bin_to_nat(incr two)  = S (S (S O))           := by {reflexivity}
example : bin_to_nat(incr three)= S (S (S (S O)))       := by {reflexivity}
example : bin_to_nat(incr four) = S (S (S (S (S O))))   := by {reflexivity}

theorem plus_n_O : ∀ n, n + O = n :=
by { intros, induction n; simp[*, plus]}

lemma p1_sa_left1 : ∀ a,  S O + a = S a := by { intros, simp [plus] }
lemma p1_sa_left2 : ∀ a, a + S O = S a := by { intros, induction a; simp [*, plus] }

lemma succ_n_n1 : ∀ x : nat,  succn x = x + S O := 
by {intros, cases x, reflexivity, simp [succn, plus], rw p1_sa_left2 }

theorem succ_comm : ∀ x y : nat,  S x + y = S (x + y) :=
by {intros,
    induction y,
    reflexivity,
    simp [plus] }

theorem plus_1_n : ∀ x : nat, S O + x = S (x) := by {intros, reflexivity}
theorem plus_n_1 : ∀ x : nat, x + S O = S (x) := by {intros, induction x, reflexivity, simp [*, succ_comm]}

theorem succ_com1 : ∀ x y : nat,  x + S y = S (x + y) :=
by {
    intros,
    induction x,
        reflexivity,
        symmetry, rw succ_comm, rw ← ih_1, symmetry, rw succ_comm
}

theorem commutativity : ∀ x y : nat, x + y = y + x :=
by {
    intros,
    induction x generalizing y,
    {simp [plus_O_n], rw plus_n_O },
    simp [plus], symmetry,
        induction y, 
            simp [plus_O_n, plus_n_O],
            simp [plus], rw ih_1_1, symmetry, simp [*, plus]
}

lemma small_assoc : ∀ x y z : nat, x + y + z = x + (y + z) :=
by {
    intros,
    induction x generalizing y z,
    reflexivity,
    simp [commutative, succ_comm], rw ih_1
}

theorem associativity : ∀ x y z : nat, (x + y) + z = x + (y + z) :=
by {
    intros,
    induction z generalizing x y,
        simp [plus_n_O],
        simp [commutativity, succ_comm, small_assoc], 
}

lemma shuffling : ∀ x y z : nat, x + y + z = x + z + y := 
by {
    intros, induction x, 
        simp [plus_O_n, commutativity],
        simp [commutativity, succ_com1], 
            rw commutativity, rw associativity, rw commutativity, rw ← ih_1,
            symmetry, rw commutativity, rw associativity, rw commutativity
}

theorem distributivity : ∀ x y z: nat, x*(y + z) = x*y + x*z :=
by {
    intros, induction x generalizing z y, 
    {reflexivity}, 
    simp [*, mult], rw ← small_assoc, symmetry, rw ← associativity, rw shuffling, rw commutativity, rw associativity, simp [commutativity, associativity],
}

lemma mult_n_1 : ∀ x : nat, x * S O = x := 
by {
    intros, induction x,
        reflexivity,
        simp [mult], rw ih_1, simp [plus_1_n]
}

lemma plus_1_1 : S O + S O = S (S O) :=
by {reflexivity}

theorem same_result : ∀ b : bin, bin_to_nat (incr b) = succn (bin_to_nat b) :=
by {
    intros,
    induction b,
    reflexivity,
    simp [*], rw ← succn, generalize h : succn (S O) * bin_to_nat a = x, simp [succ_n_n1],
    simp [*, succ_n_n1, distributivity, mult_n_1], simp [associativity], reflexivity
}


end bin


end sf_basics