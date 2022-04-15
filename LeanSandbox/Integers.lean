import LeanSandbox.Nat

structure RawInt where
  pos : Nat
  neg : Nat

private def eqv : (x y: RawInt) → Prop
  | ⟨a, b⟩, ⟨c, d⟩ => a + d = c + b

infix:50 " ~ " => eqv

private theorem eqv.refl (x: RawInt) : x ~ x := rfl
private theorem eqv.symm {x y: RawInt} (xy: x ~ y):  y ~ x := Eq.symm xy
/-
a - b   c - d   e - f
a + d = c + b
c + f = e + d
 => a + f = e + b -- the target

a + d + c + f = c + b + e + d
a + f + e + b -- done
-/
private theorem eqv.trans {x y z: RawInt} (xy: x ~ y) (yz: y ~ z): x ~ z := by
  have summed: _ := Nat.add_equations xy yz
  /- apply @Nat.subtract_to_equation_left _ _ (y.pos + y.neg) -/
  apply @Nat.add_right_cancel _ (y.pos + y.neg) _
  simp_all [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] 
  exact summed

