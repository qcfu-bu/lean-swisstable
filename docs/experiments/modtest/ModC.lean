module

public import ModA

public section

theorem tryG' (t : T) : t.g = t.x + 2 := by unfold T.g; rfl

end
