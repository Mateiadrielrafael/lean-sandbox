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


  #print Quot.ind
 
  /- 
  a - b = c - d 
  a + d = c + b

  b + c = d + a
  b - a = d - c
  -/
  private def negateRawInt.respects {x y: RawInt} (xy: x ~ y): negateRawInt x = negateRawInt y := by
    apply eqv.sound
    simp_all [eqv, Nat.add_comm] 

  def negate (τ: MyInt): MyInt :=
    Quot.liftOn τ negateRawInt @negateRawInt.respects

  private theorem raw_int_double_neg_elim: ∀x, x = negate (negate x) := by
    intro x
    induction x using Quot.ind with
    | mk a => rfl

  #print Quotient.ind₂

  private def addRawInts: RawInt → RawInt → MyInt
    | ⟨a, b⟩, ⟨c, d⟩ => {a + c, b + d}

  private def addRawInts.respects 
    {a b c d: RawInt} 
    (ac: a ~ c)
    (bd: b ~ d): addRawInts a b = addRawInts c d := by
    have summed: _ := Nat.add_equations ac bd
    apply eqv.sound
    simp [eqv, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at summed ⊢ 
    exact summed

  def add (τ: MyInt) (β: MyInt): MyInt :=
    Quotient.liftOn₂ τ β addRawInts @addRawInts.respects

  instance addMyInts: HAdd MyInt MyInt MyInt where
    hAdd := add

  #print Nat.add_comm

  theorem add.comm: ∀x y: MyInt, x + y = y + x := by
    intro x y
    simp_all [HAdd.hAdd, add] 
    induction x using Quot.ind with | mk x => 
    induction y using Quot.ind with | mk y => 
    simp [Quotient.liftOn₂]
    sorry
end MyInt 
