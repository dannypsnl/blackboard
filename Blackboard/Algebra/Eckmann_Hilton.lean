class CommOp (f : A → A → A) (x : A) : Prop where
  comm : ∀ a : A, f a x = f x a
  red : ∀ a : A, f x a = a

structure EH (A : Type u) where
  (op1 op2 : A → A → A)
  (h v : A)
  opEq1 : CommOp op1 h
  opEq2 : CommOp op2 v
  eq : ∀ a b c d : A, op1 (op2 a c) (op2 b d) = op2 (op1 a b) (op1 c d)

theorem first (eh : EH A)
  : eh.h = eh.v := by
  have C : eh.h = eh.op1 (eh.op2 eh.v eh.h) (eh.op2 eh.h eh.v) := by
    rw [eh.opEq2.comm]
    rw [eh.opEq2.red]
    rw [eh.opEq1.red]
  rw [eh.eq] at C
  rw [eh.opEq1.comm] at C
  rw [eh.opEq1.red] at C
  rw [eh.opEq2.red] at C
  exact C

theorem second (eh : EH A)
  (a b : A)
  : eh.op1 a b = eh.op2 a b := by
  have C : eh.op1 (eh.op2 a eh.v) (eh.op2 eh.v b) = eh.op2 a b := by
    rw [eh.eq]
    repeat rw [←first]
    rw [eh.opEq1.red]
    rw [eh.opEq1.comm]
    rw [eh.opEq1.red]
  rw [eh.opEq2.red] at C
  rw [eh.opEq2.comm] at C
  rw [eh.opEq2.red] at C
  exact C

theorem second_2 (eh : EH A)
  (a b : A)
  : eh.op1 a b = eh.op1 b a := by
  have C : eh.op1 (eh.op2 a eh.v) (eh.op2 b eh.v) = eh.op1 (eh.op2 b eh.v) (eh.op2 a eh.v) := by
    rw [eh.opEq2.comm]
    rw [eh.eq]
    rw [eh.eq]
    rw [←first]
    rw [eh.opEq1.red b]
    rw [eh.opEq1.comm]
    rw [eh.opEq1.red a]
    rw [eh.opEq1.comm]
    rw [eh.opEq1.red b]
  rw [eh.opEq2.comm] at C
  rw [eh.opEq2.red a] at C
  rw [eh.opEq2.comm] at C
  rw [eh.opEq2.red b] at C
  exact C
