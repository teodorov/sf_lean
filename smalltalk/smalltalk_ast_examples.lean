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

--PCObject >> #asString -> [ ^ self printString ]
#check 
    send 
        (literal (static (symbol "PCObject")))
        {message .
            selector := ">>",
            arguments := 
                [ send 
                    (literal (static (symbol "asString")))
                    { message .
                        selector := "->",
                        arguments := 
                            [ block 
                                [] 
                                [] 
                                [ return
                                    ( send 
                                        self 
                                        { message .
                                            selector := "printString",
                                            arguments := []
                                        }
                                    )  
                                ]
                            ]
                    }
                ]
        }


-- PCObject >> #at: -> {
-- 	[:index | VMProxy primitive: #at: with: { index } ].
-- 	[:index |
-- 		index isInteger
-- 			ifTrue: [ self errorSubscriptBounds: index ].
-- 		index isNumber
-- 			ifTrue: [ ^ self basicAt: index asInteger ]
-- 			ifFalse: [ self errorNonIntegerIndex ]
-- 	]
-- }