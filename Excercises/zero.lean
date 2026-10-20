
inductive nat : Type where
  | zero : nat
  | succ : nat → nat

def predecessor' : nat → nat := fun n => match n with
  | .zero => .zero
  | .succ k => k

open nat

def predecessor : nat → nat := fun n => match n with
  | zero => zero
  | succ k => k

def double : nat → nat := fun
  | zero => zero
  | succ k => succ (succ (double k))

def plus : nat → nat → nat := fun
  | n, succ m => plus (succ n) m -- reduce rhs leaving
  | n, zero   => n -- sum invariant; recurse

inductive mTrue : Prop where
 | intro : mTrue

#check mTrue -- `Type`
#check mTrue.intro -- `mTrue`

-- Lean's standard version
-- (For our implementation, use "m" prefix -- think "my")
#check True.intro

inductive mFalse : Prop
#check mFalse -- `Type`

inductive mAnd (p q : Prop) : Prop
 | intro (hp : p) (hq : q) : mAnd p q

theorem true_and_true : mAnd mTrue mTrue :=
  mAnd.intro mTrue.intro mTrue.intro

inductive mOr (p q : Prop) : Prop
 | inl (hp : p) : mOr p q -- "intro left"
 | inr (hq : q) : mOr p q -- "intro right"

open mOr mAnd

theorem true_or_false : mOr mTrue mFalse :=
  inl mTrue.intro

theorem and_of_or (p q : Prop) : (mAnd p q) → mOr p q :=
  fun hand ↦ match hand with
    | intro hp hq => mOr.inl hp

def mNeg (p : Prop) : Prop := p → mFalse

theorem neg_true_and_false :
    mNeg (mAnd mTrue mFalse) := fun h =>
  match h with
  | intro ht hf => hf



def minus : nat → nat → nat := sorry

def mul : nat → nat → nat := sorry

theorem p0 : (mTrue ∧ mTrue) ∧ mTrue := sorry

theorem p1 (p : Prop) : p → mAnd p p := sorry

theorem p2 (p : Prop) : mNeg (mAnd p (mNeg p)) := sorry

theorem p3 (p q : Prop) : mOr (mNeg p) (mNeg q) → mNeg (mAnd p q) := sorry

theorem p4 (p : Prop) : p → mNeg (mNeg p) := sorry


-- Now with the standard library:

theorem s0 (p : Prop) : ¬ ¬ (p ∨ ¬ p) := sorry

theorem orImpLeft (p q r : Prop) : ((p ∨ q) → r) → (p → r) := sorry
theorem orImpRight (p q r : Prop) : ((p ∨ q) → r) → (q → r) := sorry
theorem neg_neg_lem (p : Prop) : ¬¬(p ∨ ¬p) := sorry



variable (p q r s: Prop)

theorem q1: p ∧ q ↔ q ∧ p := sorry

theorem q2: p ∨ q ↔ q ∨ p := sorry

theorem q3: (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry

theorem q4: (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry


theorem q5: p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry

theorem q6: p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

theorem q7: (p → (q → r)) ↔ (p ∧ q → r) := sorry

theorem q8: ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry

theorem q9: ¬(p ∨ q) ↔ ¬p ∧ ¬q:= sorry


theorem q10: ¬p ∨ ¬q → ¬(p ∧ q) := sorry

theorem q11: ¬(p ∧ ¬p) := sorry

theorem q12: p ∧ ¬q → ¬(p → q) := sorry

theorem q13: ¬p → (p → q) := sorry

theorem q14: (¬p ∨ q) → (p → q) := sorry

theorem q15: p ∨ False ↔ p := sorry

theorem q16: p ∧ False ↔ False := sorry

theorem q17: ¬(p ↔ ¬p) := sorry

theorem q18: (p → q) → (¬q → ¬p) := sorry

theorem q19: (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry

theorem q20: ¬(p ∧ q) → ¬p ∨ ¬q := sorry

theorem q21: ¬(p → q) → p ∧ ¬q := sorry

theorem q22: (p → q) → (¬p ∨ q) := sorry

theorem q23: (¬q → ¬p) → (p → q) := sorry

theorem q24: p ∨ ¬p := sorry

theorem q25: (((p → q) → p) → p) := sorry

-- Predicate Logic

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

def is_even (a : Nat) := ∃ b, a = 2 * b

theorem q26 {a b} (h1: is_even a)(h2: is_even b): is_even (a+b):= sorry

theorem q27 : (∃ _ : α, r) → r := sorry

theorem q28 (a : α) : r → (∃ _ : α, r) := sorry

theorem q29 : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry

theorem q30 : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

theorem q31 : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry

theorem q32 : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry

theorem q33: (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry

theorem q34 : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

theorem q35 : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry

theorem q36: (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry

theorem q37 (a : α): (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
