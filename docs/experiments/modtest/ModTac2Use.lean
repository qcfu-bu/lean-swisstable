module

public import ModTac2

public section

theorem t2 (n : Nat) (h : n + 0 = 3) : n = 3 := by my_tac2 [size] at h ⊢ using h

end
