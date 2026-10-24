module

public import ModA

public section

set_option trace.compiler.ir.result true in
def useF (n : Nat) : Nat := (T.mk n).f + T.app (· * 3) (T.mk n)

end
