import ModA

theorem tryG'' (t : T) : t.g = t.x + 2 := rfl
theorem tryG''' (t : T) : t.g = t.x + 2 := by unfold T.g; rfl
