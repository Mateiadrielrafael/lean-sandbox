theorem add_equations: ∀{a b c d: Nat}, a = b → c = d → a + c = b + d := by
  intro a b c d ab cd
  rw [ab, cd]

theorem add_to_equation: ∀{a b c: Nat}, a = b → a + c = b + c := by
  intro a b c ab
  exact add_equations ab rfl

theorem succ_equation : ∀{a b: Nat}, Nat.succ a = Nat.succ b → a = b := by
  intro a b
  apply Eq.mp -- (a + 1 = b + 1) = a + b
  apply Nat.succ.injEq -- this was already here?

inductive A : Nat -> Type
  | ooo: (n: Nat) → A n 

theorem subtract_to_equation: ∀{a b c: Nat}, a + c = b + c → a = b := by
  intro a b c acbc
  induction c with
  | zero => 
    repeat rw [Nat.add_zero] at acbc
    exact acbc
  | succ pc inner => 
    /- 
      a + S pc = b + S pc -- comm
      S pc + a = S pc + b -- addition definition
      S (pc + a) = S (pc + b) -- injective constructor
      pc + a = pc + b
    -/
    rw [Nat.add_comm a (Nat.succ pc), Nat.add_comm b (Nat.succ pc)] at acbc
    simp [Nat.succ_add, Nat.add_comm] at acbc
    exact (inner acbc)

#print subtract_to_equation

theorem add_equation_both_sides: ∀{a b c: Nat}, (a = b) ↔ (a + c = b + c) := by
  intro a b c
  apply Iff.intro
  . exact add_to_equation
  . exact subtract_to_equation 
