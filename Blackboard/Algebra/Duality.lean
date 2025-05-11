variable
  {K : Type u}
  {V : Type v}
  {W : Type l}

def 𝕀 (B : V × W → K) : V → (W -> K) :=
  fun v w => B (v, w)
def down (L : V → (W → K)) : V × W → K :=
  fun (v, w) => (L v) w

theorem adjunction_map_is_the_generator_map_itself (L : V → (W → K)) : 𝕀 (down L) = L := by
  exact rfl
