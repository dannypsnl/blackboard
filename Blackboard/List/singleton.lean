variable
  {α : Type}
  [BEq α]
  [LawfulBEq α]

def s {T : Type} (x : T) : List T := [x]

theorem size_is_one : (s x).length = 1
  := by
  exact rfl

theorem has_x {x : α}
  : (s x).elem x = true
  := by
  simp [List.elem]
  exact List.mem_of_mem_head? rfl
