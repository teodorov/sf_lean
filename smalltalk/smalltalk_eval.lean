import .smalltalk_ast_mi

def toBytes : string → list char := λ str, string.to_list str

inductive ObjectHeader
| clazz : ℕ → ObjectHeader
.

inductive ObjectPointer
| DirectPointer : ℕ → ObjectPointer
| SmallInteger : ℤ → ObjectPointer
| Character : char → ObjectPointer
--| SmallFloat : SmallFloat → ObjectPointer
.

inductive Object 
| new (header: ObjectHeader) (fields: list ObjectPointer)
| variable_byte (header: ObjectHeader) (data: list char)

def MetaclassAddr := 3
def ArrayClassAddr := 4

def behaviorNameSymbolAddr := 1.    --the address of #Behavior symbol object

def TODO_addr := 3.     --the address of an static literal array 
def nilAddr := 0
def ClassDescriptionClassAddr := 5

def ObjectClassAddr := 0.           --the address of the Object class

def MetaclassClass := Object.new (ObjectHeader.clazz ClassDescriptionClassAddr) [
    (ObjectPointer.DirectPointer ObjectClassAddr),                --superclass: nil
    (ObjectPointer.DirectPointer nilAddr),                        --instance variables: #thisClass
    (ObjectPointer.DirectPointer nilAddr)                         --method dictionary: @TODO
]
def MetaclassClassAddr := 5

def SymbolClassAddr := 5
def SymbolSymbol := Object.variable_byte (ObjectHeader.clazz SymbolClassAddr) (toBytes "Symbol")
def SymbolSymbolAddr := 5
def SymbolClassMetaclass := Object.new (ObjectHeader.clazz MetaclassClassAddr) [
    (ObjectPointer.DirectPointer ObjectClassAddr),                --superclass: nil
    (ObjectPointer.DirectPointer nilAddr),                        --instance variables: nil
    (ObjectPointer.DirectPointer nilAddr),                        --method dictionary: @TODO
    (ObjectPointer.DirectPointer SymbolClassAddr)                 --thisClass: SymbolClass
]
def SymbolClassMetaclassAddr := 5
def SymbolClass := Object.new (ObjectHeader.clazz SymbolClassMetaclassAddr) [
    (ObjectPointer.DirectPointer SymbolSymbolAddr),               --name: #Symbol
    (ObjectPointer.DirectPointer ObjectClassAddr),                --superclass: nil
    (ObjectPointer.DirectPointer nilAddr),                        --instance variables: nil
    (ObjectPointer.DirectPointer nilAddr)                         --method dictionary: @TODO
]

def ObjectSymbol := Object.variable_byte (ObjectHeader.clazz SymbolClassAddr) (toBytes "Object")
def ObjectSymbolAddr := 5
def ObjectClassMetaclass := Object.new (ObjectHeader.clazz MetaclassClassAddr) []
def ObjectClassMetaclassAddr := 5
def ObjectClass := Object.new (ObjectHeader.clazz ObjectClassMetaclassAddr) [
    (ObjectPointer.DirectPointer ObjectSymbolAddr),               --name: #Object
    (ObjectPointer.DirectPointer nilAddr),                        --superclass: nil
    (ObjectPointer.DirectPointer nilAddr),                        --instance variables: nil
    (ObjectPointer.DirectPointer nilAddr)                         --method dictionary: @TODO
]

def BehaviorSymbol := Object.variable_byte (ObjectHeader.clazz SymbolClassAddr) (toBytes "Behavior")
def BehaviorSymbolAddr := 5
def BehaviorClassMetaclass := Object.new (ObjectHeader.clazz MetaclassClassAddr) []
def BehaviorClassMetaclassAddr := 5
def BehaviorClass := Object.new (ObjectHeader.clazz BehaviorClassMetaclassAddr) [
    (ObjectPointer.DirectPointer BehaviorSymbolAddr),       --name: #Behavior
    (ObjectPointer.DirectPointer ObjectClassAddr),          --superclass: Object
    (ObjectPointer.DirectPointer TODO_addr),                --instance variables: #superclass #methodDict
    (ObjectPointer.DirectPointer nilAddr)                   --method dictionary: @TODO
]
def BehaviorClassAddr := 5

def ClassDescriptionSymbol := Object.variable_byte (ObjectHeader.clazz SymbolClassAddr) (toBytes "ClassDescription")
def ClassDescriptionSymbolAddr := 5
def ClassDescriptionClassMetaclass := Object.new (ObjectHeader.clazz MetaclassClassAddr) []
def ClassDescriptionClassMetaclassAddr := 5
def ClassDescriptionClass := Object.new (ObjectHeader.clazz ClassDescriptionClassMetaclassAddr) [
    (ObjectPointer.DirectPointer ClassDescriptionSymbolAddr),--name: #ClassDescription
    (ObjectPointer.DirectPointer BehaviorClassAddr),         --superclass: Behavior
    (ObjectPointer.DirectPointer TODO_addr),                 --instance variables: #instanceVariables
    (ObjectPointer.DirectPointer nilAddr)                    --method dictionary: @TODO
]

def ClassSymbol := Object.variable_byte (ObjectHeader.clazz SymbolClassAddr) (toBytes "Class")
def ClassSymbolAddr := 5
def ClassClassMetaclass := Object.new (ObjectHeader.clazz MetaclassClassAddr) []
def ClassClassMetaclassAddr := 5
def ClassClass := Object.new (ObjectHeader.clazz ClassClassMetaclassAddr) [
    (ObjectPointer.DirectPointer ClassDescriptionSymbolAddr),--name: #Class
    (ObjectPointer.DirectPointer ClassDescriptionClassAddr), --superclass: ClassDescription
    (ObjectPointer.DirectPointer TODO_addr),                 --instance variables: #name
    (ObjectPointer.DirectPointer nilAddr)                    --method dictionary: @TODO
]

def UndefinedObjectSymbol := Object.variable_byte (ObjectHeader.clazz SymbolClassAddr) (toBytes "UndefinedObject")
def UndefinedObjectSymbolAddr := 5
def UndefinedObjectClassMetaclass := Object.new (ObjectHeader.clazz MetaclassClassAddr) []
def UndefinedObjectClassMetaclassAddr := 5
def UndefinedObjectClass  := Object.new (ObjectHeader.clazz UndefinedObjectClassMetaclassAddr) [
    (ObjectPointer.DirectPointer UndefinedObjectSymbolAddr),--name: #UndefinedObject
    (ObjectPointer.DirectPointer ObjectClassAddr),          --superclass: Object
    (ObjectPointer.DirectPointer nilAddr),                  --instance variables: nil
    (ObjectPointer.DirectPointer nilAddr)                   --method dictionary: @TODO
]
def UndefinedObjectClassAddr := 5
def nil : Object := Object.new (ObjectHeader.clazz UndefinedObjectClassAddr) []

inductive Object1 
| nil : Object1
| number : Number → Object1
| symbol : String → Object1
| string : String → Object1
| fields : list Object1 → Object1
.

structure Context := (symbols : set Object1)

open static_literal

def eval (ctx : Context) : static_literal → Object1
| nil := Object1.nil
| (numeric v) := Object1.number v
| (symbol v) := Object1.symbol v
| (string v) := Object1.string v
| (boolean v) := sorry 
| (character v) := sorry
| (byte v) := sorry
| (array v) := sorry

