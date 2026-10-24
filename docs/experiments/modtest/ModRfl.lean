module

public section

def g (n : Nat) : Nat := n + 2

/-- Fails: an exported theorem may not unfold a non-exposed definition by `rfl`. -/
theorem g_eq_rfl (n : Nat) : g n = n + 2 := rfl

/-- Works: `unfold` uses the equation lemma, which the module can see. -/
theorem g_eq_unfold (n : Nat) : g n = n + 2 := by unfold g; rfl

end
