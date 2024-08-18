inductive I where
  | zero : I
  | pos : I → I
  | neg : I → I

def rel : I → I → Prop
  | .pos (.neg x), .neg (.pos y) => x = y
  | .neg (.pos x), .pos (.neg y) => x = y
  | x, y => x = y

abbrev MInt := Quot rel

theorem t : Quot.mk rel (.pos (.neg zero)) = Quot.mk rel (.neg (.pos zero))
  := by
  exact Quot.sound rfl
