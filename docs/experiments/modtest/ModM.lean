module

public import ModA

public section

/-- Not exposed: a term proof that needs to unfold it fails in an exported theorem. -/
def wrapHidden (t : T) : Nat := t.g
/-- Exposed: the same proof works. -/
@[expose] def wrapShown (t : T) : Nat := t.g

theorem base (t : T) : t.g = t.g := rfl

theorem viaHidden (t : T) : wrapHidden t = t.g := base t
theorem viaShown (t : T) : wrapShown t = t.g := base t

end
