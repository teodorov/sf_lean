prelude
import init.data.fin.basic init.data.char

private structure symbol_imp := (data : list char)
def Symbol := symbol_imp
namespace Symbol
    def mk (d : string) : Symbol := { data := string.to_list d }
end Symbol
notation `#` d := Symbol.mk d



private structure character_imp := (data : char)
def Character := character_imp
namespace Character
    def mk (c : char) : Character := { data := c }
end Character
notation `$` c := Character.mk c

private structure boolean_imp := bool 
def Boolean := bool

private structure Number_imp := (data : ℕ)
def Number := Number_imp
namespace Number
    def number_has_one : Number := { data := 1 }
    def number_has_add (a: Number) (b: Number) : Number := { data := a.data + b.data }
end Number
instance : has_one Number := ⟨ Number.number_has_one ⟩ 
instance : has_add Number := ⟨ Number.number_has_add ⟩ 

def Byte_size : nat := nat.succ 255
def Byte := fin Byte_size

instance : has_sizeof Byte := ⟨fin.sizeof _⟩ 
instance : decidable_eq Byte := 
    have decidable_eq (fin Byte_size), from fin.decidable_eq _,
    this

namespace Byte
    lemma zero_lt_byte_sz : 0 < 256 :=
    nat.zero_lt_succ _
    @[pattern] def of_nat (n : nat) : Byte :=
    if h : n < 256 then fin.mk n h else fin.mk 0 zero_lt_byte_sz

    def to_nat (c : Byte) : nat := fin.val c

    def byte_has_add (a : Byte) (b : Byte) := of_nat (((to_nat a) + (to_nat b)) % Byte_size)
end Byte

instance : has_one Byte := ⟨ Byte.of_nat(1) ⟩
instance : has_add Byte := ⟨ Byte.byte_has_add ⟩ 
def String := string