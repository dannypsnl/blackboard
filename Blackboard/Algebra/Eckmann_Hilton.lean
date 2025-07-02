structure CommOp (f : A → A → A) (x : A) where
  eq1 : ∀ a : A, f a x = f x a
  eq2 : ∀ a : A, f x a = a

structure EH (A : Type u) where
  (op1 op2 : A → A → A)
  (h v : A)
  comm1 : CommOp op1 h
  comm2 : CommOp op2 v
  eq : ∀ a b c d : A, op1 (op2 a c) (op2 b d) = op2 (op1 a b) (op1 c d)

theorem first (eh : EH A)
  : eh.h = eh.v := by
  have C : eh.h = eh.op1 (eh.op2 eh.v eh.h) (eh.op2 eh.h eh.v) := by
    rw [eh.comm2.eq1]
    rw [eh.comm2.eq2]
    rw [eh.comm1.eq2]
  rw [eh.eq] at C
  rw [eh.comm1.eq1] at C
  rw [eh.comm1.eq2] at C
  rw [eh.comm2.eq2] at C
  exact C

theorem second (eh : EH A)
  (a b : A)
  : eh.op1 a b = eh.op1 b a := by
  sorry
