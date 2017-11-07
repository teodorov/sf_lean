prelude
import init.data.fin.basic init.data.char

def String := string
def Symbol := string
def Character := char
def Boolean := bool


@[derive decidable_eq]
structure Number_imp := (data: int)
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
