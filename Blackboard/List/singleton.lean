variable
  {α : Type}
  [BEq α]
  [LawfulBEq α]

def s {T : Type} (x : T) : List T := [x]

theorem size_one {x : α}
  : (s x).length = 1
  := by
  rfl

theorem has_x {x : α}
  : (s x).elem x = true
  := by
  simp [List.elem]
