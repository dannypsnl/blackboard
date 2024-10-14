variable
  (a b c : Nat)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← Nat.add_assoc, Nat.add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [Nat.mul_comm b a, ←Nat.two_mul]
