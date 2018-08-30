import system.io

def fib : ℕ → ℕ 
| 0 := 1
| 1 := 1
| (n+2) := fib n + fib (n + 1)


def main : io unit :=
    io.print_ln "hello" >> 
    io.print_ln ("toto", 6) >>
    io.print_ln (fib 7)

#eval fib 7

--lean --run simple.lean