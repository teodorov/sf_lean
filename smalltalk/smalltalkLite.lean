-- Starting point is the SmalltalkLite [1]. 
-- [1] Bergel, Alexandre, et al. "Stateful traits and their formalization." 
--     Computer Languages, Systems & Structures 34.2 (2008): 83-108.

inductive value 
| object    --the only value is an object

inductive exp : Type
| var       --variable reference
| new       --object creation
| self      --self send
| super     --super send
| send      --normal send
| nil       --nil
| letz      --temporaries
| block     --abstraction
