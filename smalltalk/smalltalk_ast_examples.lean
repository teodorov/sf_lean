import .smalltalk_ast_mi

open static_literal
open literal
open expression
open statement

#check expression.reference "xxx"
#check assignment
#check numeric 23
#check assignment ("xxx")  (literal (static (symbol "xxx")))
#check assignment "xxx" (literal (static (symbol "xxx")))

