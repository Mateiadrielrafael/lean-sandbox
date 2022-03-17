-- single line comment

def m: Nat := 1

#check m
#check m

#check (m + m)
#eval (m + m)

#check Nat × Nat

def Γ := 2 + m
 

def double (a: Nat) := a + a

#eval double (double 3)

section composition
  variable (α β γ: Type)

  def compose (f: α → β) (g: β → γ): (α -> γ) := fun x: α => g (f x)
end composition

def quadruble := compose _ _ _ double double

#print compose

section composition'
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose' := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end composition'

def a: Nat := 3

#eval double a
#print compose'
#check (Nat : Sort 1)
#check (Prop : Sort 1)
#check (Prop : Type)


section proofs 
  theorem hmm (α: Prop) (β: Prop): Prop := α
  theorem hmm2 : Prop -> Prop -> Prop := 
    fun α β => show Prop from α

  theorem hmm3 (hm: α): α := hm

  axiom myProof: Prop

  #check hmm
  #check hmm2
  #check hmm3 myProof
  #check @hmm3
  #check @hmm3 myProof
end proofs

section logic
  variable {α β π: Prop}
  variable (ha: α) (hb: β)

  theorem pair: α -> β -> α ∧ β := fun a b => And.intro a b
  theorem unpair: (α → β → π) → α ∧ β → π := fun f a => 
    show π from f (And.left a) (And.right a)

  theorem pairsCommute: (α ∧ β) → (β ∧ α) := fun p => 
    show (β ∧ α) from And.intro (And.right p) (And.left p)

  example (h: α ∧ β): β ∧ α := ⟨h.right, h.left⟩

  theorem thrice: (f: α) -> α ∧ α ∧ α := fun f => ⟨ f, f, f ⟩

  theorem negateFunc: (β → α) → ¬α → ¬β := 
    fun f notₐ b => 
      show False from notₐ (f b)

  #print pairsCommute 
  #check (⟨ha, hb⟩: α ∧ β)

  theorem exFalso: (α ∧ ¬ α) → β :=
    fun contradiction => 
      show β from (contradiction.right contradiction.left).elim

  theorem pairIso: α ∧ β ↔ β ∧ α := ⟨ pairsCommute, pairsCommute ⟩
end logic

section classical
  open Classical 

  variable (α : Prop)

  def dneT: Prop = ¬¬α → α

  theorem doubleNegation: α ↔ ¬¬α :=
    suffices l: α → ¬¬α from 
    suffices r: ¬¬α → α from ⟨ l, r ⟩
    show dneT from fun doubleNegA => (em α).elim
      (fun p: α => p)
      (fun p: ¬α => absurd p doubleNegA)
    show α → ¬¬α from (fun a f => f a)

  #print byCases

  theorem dne: dneT := fun nnₚ =>
    byCases id
      (fun nₚ => nnₚ nₚ)

  #print byContradiction

  theorem dne': dneT := fun nnₚ =>
    byContradiction fun nₚ => nnₚ nₚ 
end classical

section exercises
  variable (p q r : Prop)

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := sorry
  example : p ∨ q ↔ q ∨ p := sorry

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
  example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
  example : ¬(p ∧ ¬p) := sorry
  example : p ∧ ¬q → ¬(p → q) := sorry
  example : ¬p → (p → q) := sorry
  example : (¬p ∨ q) → (p → q) := sorry
  example : p ∨ False ↔ p := sorry
  example : p ∧ False ↔ False := sorry
  example : (p → q) → (¬q → ¬p) := sorry
end exercises

