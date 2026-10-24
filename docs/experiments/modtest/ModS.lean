module

public section

theorem fooS : 1 + 1 = 2 := sorry

theorem barS : 2 = 2 := by exact (fun _ => rfl) fooS

end
