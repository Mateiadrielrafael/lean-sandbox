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
  apply @Nat.add_right_cancel _ (y.pos + y.neg) _
  simp_all [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] 

private theorem is_equivalence: Equivalence eqv := 
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }

instance rawIntSetoid: Setoid RawInt where
  r := eqv
  iseqv := is_equivalence

def MyInt: Type := 
  Quotient rawIntSetoid

private theorem eqv.sound: x ~ y → Quotient.mk' x = Quotient.mk' y  := Quot.sound

def MyInt.mk (pos neg: Nat): MyInt := Quotient.mk' ⟨pos, neg⟩

notation "{ " a₁ ", " a₂ " }" => MyInt.mk a₁ a₂

namespace MyInt
  private def negateRawInt: RawInt → MyInt
    | ⟨pos, neg⟩ => {neg, pos}


  #print Quot.sound
 
  /- 
  a - b = c - d 
  a + d = c + b

  b + c = d + a
  b - a = d - c
  -/
  private def negateRawInt.respects {x y: RawInt} (xy: x ~ y): negateRawInt x = negateRawInt y := by
    have t: {x.neg, x.pos} = negateRawInt x := rfl
    apply eqv.sound
    simp_all [eqv, Nat.add_comm] 

  def negate (τ: MyInt): MyInt :=
    Quot.liftOn τ negateRawInt @negateRawInt.respects

  private theorem raw_int_double_neg_elim: ∀x, x = negate (negate x) := by
    intro x
    sorry
end MyInt 
