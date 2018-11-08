-- Generalized Transition Relation

namespace gtr

structure GTR (C : Type) (F : Type) (E : Type):=
    (initial : set C)
    (steps (source: C) : set F)
    (doStep (source: C) (fireable: F) : set (set E × C))

end gtr