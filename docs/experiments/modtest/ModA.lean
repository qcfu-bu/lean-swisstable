module

public section

structure T where
  x : Nat

@[inline] def T.f (t : T) : Nat := t.x + 1

@[specialize] def T.app (f : Nat → Nat) (t : T) : Nat := f (f t.x)

def T.g (t : T) : Nat := t.x + 2

end
