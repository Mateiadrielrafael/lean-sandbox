import LeanSandbox.Nat

macro "nat_ring"  : tactic => `(simp_all [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm])
macro "quotient_madness" : tactic => `(simp [Quotient.mk', Quotient.mk, Quotient.liftOn₂, Quotient.lift₂, Quotient.lift])

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
  nat_ring

private theorem is_equivalence: Equivalence eqv := 
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }

instance rawIntSetoid: Setoid RawInt where
  r := eqv
  iseqv := is_equivalence

def MyInt: Type := 
  Quotient rawIntSetoid

private theorem eqv.sound: x ~ y → Quotient.mk' x = Quotient.mk' y  := Quot.sound

@[simp]
def MyInt.mk (pos neg: Nat): MyInt := Quotient.mk' ⟨pos, neg⟩

notation "{ " a₁ ", " a₂ " }" => MyInt.mk a₁ a₂

@[simp, inline]
private def MyInt.ofRawInt(raw: RawInt) := MyInt.mk raw.pos raw.neg

@[simp, inline]
private def RawInt.ofNat(nat: Nat): RawInt := ⟨nat, 0⟩

@[simp, inline]
private def MyInt.ofNat(nat: Nat): MyInt := {nat, 0}

private instance rawIntOfNat: OfNat RawInt n where
  ofNat := RawInt.ofNat n

instance myIntOfNat: OfNat MyInt n where
  ofNat := MyInt.ofNat n

namespace MyInt
  private def negateRawInt: RawInt → MyInt
    | ⟨pos, neg⟩ => {neg, pos}

  /- 
  a - b = c - d 
  a + d = c + b

  b + c = d + a
  b - a = d - c
  -/
  private theorem negateRawInt.respects {x y: RawInt} (xy: x ~ y): negateRawInt x = negateRawInt y := by
    apply eqv.sound
    simp_all [eqv, Nat.add_comm] 

  def negate (τ: MyInt): MyInt :=
    Quotient.liftOn τ negateRawInt @negateRawInt.respects

  instance negMyInt: Neg MyInt where
    neg := negate

  private theorem double_neg_elim: ∀x, x = negate (negate x) := by
    intro x
    induction x using Quotient.ind
    rfl

  private def addRawInts: RawInt → RawInt → MyInt
    | ⟨a, b⟩, ⟨c, d⟩ => {a + c, b + d}

  private theorem addRawInts.respects 
    {a b c d: RawInt} 
    (ac: a ~ c)
    (bd: b ~ d): addRawInts a b = addRawInts c d := by
    have summed: _ := Nat.add_equations ac bd
    apply eqv.sound
    simp [eqv] at summed ⊢ 
    nat_ring 

  private theorem addRawInts.comm (a b: RawInt): addRawInts a b = addRawInts b a := by
    simp_all [addRawInts, Nat.add_comm]

  def add (τ β: MyInt): MyInt :=
    Quotient.liftOn₂ τ β addRawInts @addRawInts.respects

  private instance hAddRawInts: HAdd RawInt RawInt MyInt where
    hAdd := addRawInts
  instance hAddMyInts: HAdd MyInt MyInt MyInt where
    hAdd := add

  def sub (a b: MyInt): MyInt := a + (-b)

  instance hSubMyInt: HSub MyInt MyInt MyInt where
    hSub := sub

  @[simp]
  theorem sub.x_minus_x_is_zero (a: MyInt): a - a = 0 := by
    simp_all [HSub.hSub, sub, HAdd.hAdd, add, negate, Neg.neg, MyInt.ofNat] 
    induction a using Quotient.ind
    apply eqv.sound
    simp [eqv]
    apply Nat.add_comm

  theorem add.comm: ∀x y: MyInt, x + y = y + x := by
    intro x y
    simp_all [HAdd.hAdd, add] 
    induction x, y using Quotient.ind₂
    quotient_madness
    apply addRawInts.comm

  theorem add.assoc(x y z: MyInt): x + (y + z) = (x + y) + z := by
    simp_all [HAdd.hAdd, add] 

    induction x, y using Quotient.ind₂
    induction z using Quotient.ind 

    apply eqv.sound
    simp [eqv]
    nat_ring

  @[simp]
  theorem add.zero(x: MyInt): x + 0 = 0 + x := by
    simp_all [HAdd.hAdd, add]
    induction x using Quotient.ind
    apply eqv.sound
    simp [eqv]

  /-
  (a - b) * (c - d)
  ac - bc - ad + bd
  -/
  private def multiplyRawInts: RawInt → RawInt → MyInt
    | ⟨a, b⟩, ⟨c, d⟩ => {a * c + b * d, b * c + a * d}

  /-
  ac : c.neg + a.pos = a.neg + c.pos
  bd : d.neg + b.pos = b.neg + d.pos
  ⊢ a.neg * b.neg + (a.pos * b.pos + (c.pos * d.neg + c.neg * d.pos)) =
    c.neg * d.neg + (a.pos * b.neg + (a.neg * b.pos + c.pos * d.pos))

  a - b c - d e - f g - h

  f + a = b + e
  h + c = d + g

  bd + ac + eh + fg = fh + ad + bc + eg

  bd + ac + fc + eh + fg + ec = fh + ad + bc + ec + eg + fc
  + af + ce
  bd + c(a + f) + eh + fg + ec = fh + ad + c(b + e) + eg + fc
  bd + eh + fg + ec = fh + ad + eg + fc
  bd + e(h + c) + fg = f(h + c) + ad + eg
  + bg + ag
  b(d + g) + e(h + c) + fg + ag = f(h + c) + a(d + g) + bg + eg
  (h + c)(b + e) + g(a + f) = (h + c)(f + a) + g(b + e)
  (h + c)(f + a) + g()

  a = b + e - f
  bd + bc + ec + fd + eh + fg = fh + bd + ed + fc + eg
  ec + fd + eh + fg = fh + ed + fc + eg
  c = d + g - h
  True

  a - b c - d e - f g - h
  -/
  private theorem multiplyRawInts.respects 
    {x y z w: RawInt} 
    (xz: x ~ z)
    (yw: y ~ w): multiplyRawInts x y = multiplyRawInts z w := by
    apply eqv.sound
    simp_all [eqv] 
    apply @Nat.subtract_to_equation_left _ _ 
      (y.pos * z.neg + y.pos * z.pos + x.neg * w.pos + x.pos * w.pos) 
    nat_ring
    have start: 0 = 0 := rfl;
    -- ca + cf => c(a + f)
    -- y.pos (x.pos + z.neg)
    /- rw [Nat.mul_comm x.pos y.pos, Nat.mul_comm x.neg y.pos] -/
    /- rw [<-Nat.add_assoc (y.pos * x.pos), <-Nat.add_assoc (y.pos * x.neg)] -/
    /- rw [<-Nat.left_distrib y.pos x.pos z.neg, <-Nat.left_distrib y.pos x.neg z.pos] -/
    -- cb + ce => c(b + e)
    -- y.pos (x.neg + z.pos)
    sorry

  #print Nat.multiply_equation_left
end MyInt 
