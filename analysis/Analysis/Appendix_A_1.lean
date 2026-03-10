import Mathlib.Tactic

/-!
# Analysis I, Appendix A.1: Mathematical Statements

An introduction to mathematical statements.  Showcases some basic tactics and Lean syntax.

-/


-- Example A.1.1. What the textbook calls "statements" are objects of type `Prop` in Lean. Also, in
-- Lean we tend to assign "junk" values to expressions that might normally be considered undefined,
-- so discussions regarding undefined terms in the textbook should be adjusted accordingly.

#check 2 + 2 = 4
#check 2 + 2 = 5

/-- Every well-formed statement is either true or false... -/
example (P : Prop) : P=true ∨ P=false := by
  rewrite [Bool.coe_false]
  simp only [refl]
  simp only [eq_iff_iff]
  rewrite [iff_true, iff_false]
  rewrite [← imp_iff_or_not]
  intro p
  exact p

/-- .. but not both. -/
example (P : Prop) : ¬ (P=true ∧ P=false) := by
  rewrite [Bool.coe_false]
  simp only [refl]
  simp only [eq_iff_iff]
  rewrite [iff_true, iff_false]
  simp only [and_not_self]
  simp only [not_false_eq_true]

-- Note: `P=true` and `P=false` simplify to `P` and `¬P` respectively.

/-- To prove that a statement is true, it suffices to show that it is not false. -/
example {P: Prop} (h: P≠false) : P=true := by
  rewrite [Bool.coe_false] at h
  simp only [refl]
  rewrite [ne_eq] at h
  rewrite [eq_iff_iff] at *
  rewrite [iff_false] at h
  rewrite [not_not] at h
  rewrite [iff_true]
  exact h

/-- while to show that a statement is false, it suffices to show that it is not true. -/
example {P : Prop} (h : P≠true) : P=false := by
  simp only [refl] at h
  rewrite [ne_eq] at h
  rewrite [eq_iff_iff] at *
  rewrite [iff_true] at h
  rewrite [Bool.coe_false]
  rewrite [iff_false]
  exact h

/-- This statement is true, but unlikely to be very useful. -/
example : 2 = 2 := rfl

/-- This statement is also true, but not very efficient. -/
example : 4 ≤ 4 := by norm_num

/- This is an expression, not a statement. -/
#check 2 + 3 * 5

/- This is a statement, not an expression. -/
#check 2 + 3 * 5 = 17

#check Prime (30 + 5)

#check 30 + 5 ≤ 42 - 7

/-- Conjunction -/
example {X Y : Prop} (hX : X) (hY : Y) : X ∧ Y := by
  constructor
  · exact hX
  exact hY

example {X Y : Prop} (hXY : X ∧ Y) : X := by
  exact hXY.left

example {X Y : Prop} (hXY : X ∧ Y) : Y := by
  exact hXY.right

example {X Y : Prop} (hX : ¬ X) : ¬ (X ∧ Y) := by
  contrapose! hX
  exact hX.left

example {X Y : Prop} (hY : ¬ Y) : ¬ (X ∧ Y) := by
  contrapose! hY
  exact hY.right

example : 2+2=4 ∧ 3+3=6 := by
  constructor
  · rfl
  rfl

/-- Disjunction -/
example {X Y : Prop} (hX : X) : X ∨ Y := by
  left
  exact hX

example {X Y : Prop} (hY : Y) : X ∨ Y := by
  right
  exact hY

example {X Y : Prop} (hX : ¬X) (hY : ¬Y) : ¬(X ∨ Y) := by
  rewrite [not_or]
  constructor
  · exact hX
  exact hY

example : 2+2=4 ∨ 3+3=5 := by
  left
  rfl

example : ¬(2+2=5 ∨ 3+3=5) := by
  simp only [Nat.reduceAdd]
  simp only [Nat.reduceEqDiff]
  rewrite [or_self]
  simp only [not_false_eq_true]

example : 2+2=4 ∨ 3+3=6 := by
  left
  rfl

example : 2+2=4 ∧ 3+3=6 := by
  constructor
  · rfl
  rfl

example : 2+2=4 ∨ 2353+5931=7284 := by
  left
  rfl

#check Xor'

/-- Negation -/
example {X : Prop} : ¬ X=true ↔ X=false := by
  rewrite [Bool.coe_false]
  simp only [refl]
  simp only [eq_iff_iff]
  simp only [iff_true, iff_false]

example {X : Prop} : ¬ X = false ↔ X = true := by
  rewrite [Bool.coe_false]
  simp only [refl]
  simp only [eq_iff_iff]
  rewrite [iff_true, iff_false]
  simp only [not_not]

example : ¬ 2+2=5 := by
  simp only [Nat.reduceAdd]
  simp only [Nat.reduceEqDiff]
  trivial

example : 2+2≠5 := by
  rewrite [ne_eq]
  simp only [Nat.reduceAdd]
  simp only [Nat.reduceEqDiff]
  trivial

example (Jane_black_hair Jane_blue_eyes : Prop) :
  ¬(Jane_black_hair ∧ Jane_blue_eyes) ↔ ¬ Jane_black_hair ∨ ¬ Jane_blue_eyes := by
  rewrite [not_and_or]
  rfl

example (x : ℤ) : ¬(Even x ∧ x ≥ 0) ↔ Odd x ∨ x < 0 := by
  rewrite [not_and_or]
  simp only [Int.not_even_iff_odd, Int.not_le]

example (x : ℤ) : ¬(x ≥ 2 ∧ x ≤ 6) ↔ x < 2 ∨ x > 6 := by
  rewrite [not_and_or]
  simp only [Int.not_le]

example (John_brown_hair John_black_hair : Prop) :
  ¬(John_brown_hair ∨ John_black_hair) ↔ ¬John_brown_hair ∧ ¬John_black_hair := by
  simp only [not_or]

example (x : ℝ) : ¬(x ≥ 1 ∧ x ≤ -1) ↔ x < 1 ∨ x > -1 := by
  rewrite [not_and_or]
  simp only [not_le]

example (x : ℤ) : ¬(Even x ∨ Odd x) ↔ ¬ Even x ∧ ¬ Odd x := by
  simp only [not_or]

example (X : Prop) : ¬ ¬ X ↔ X := by
  simp only [not_not]

/-- If and only if (iff) -/
example {X Y : Prop} (hXY : X ↔ Y) (hX : X) : Y := by
  rewrite [hXY] at hX
  exact hX

example {X Y : Prop} (hXY : X ↔ Y) (hY : Y) : X := by
  rewrite [←hXY] at hY
  exact hY

example {X Y : Prop} (hXY : X ↔ Y) (hX : X) : Y := by
  exact hXY.mp hX

example {X Y : Prop} (hXY : X ↔ Y) (hY : Y) : X := by
  exact hXY.mpr hY

example {X Y : Prop} (hXY : X ↔ Y) : X=Y := by
  simp only [hXY]

example (x : ℝ) : x=3 ↔ 2*x=6 := by
  constructor
  · intro h
    linarith
  intro h
  linarith

example : ¬ ∀ x : ℝ, x = 3 ↔ x^2 = 9 := by
  rewrite [not_forall]
  use -3
  norm_cast

example {X Y : Prop} (hXY : X ↔ Y) (hX : ¬X) : ¬Y := by
  by_contra this
  rw [←hXY] at this
  contradiction

example : 2+2=5 ↔ 4+4=10 := by
  simp only [Nat.reduceAdd]
  simp only [Nat.reduceEqDiff]

example {X Y Z : Prop} (hXY : X ↔ Y) (hXZ : X ↔ Z) : [X, Y, Z].TFAE := by
  tfae_have 1 ↔ 2 := by exact hXY  -- This line is optional
  tfae_have 1 ↔ 3 := by exact hXZ  -- This line is optional
  tfae_finish

/-- Note for the `.out` method that one indexes starting from 0, in contrast to the `tfae_have`
    tactic. -/
example {X Y Z : Prop} (h : [X, Y, Z].TFAE) : X ↔ Y := by
  exact h.out 0 1

/-- Exercise A.1.1 -/
example {X Y : Prop} : ¬((X ∨ Y) ∧ ¬(X ∧ Y)) ↔ (X ↔ Y) := by
  rewrite [not_and, not_not]
  constructor
  · intro h
    constructor
    · intro x
      have xory : X ∨ Y
      left
      exact x
      exact (h xory).right
    intro y
    have xory : X ∨ Y
    right
    exact y
    exact (h xory).left
  intro h g
  obtain x | y := g
  · exact ⟨x, h.mp x⟩
  exact ⟨h.mpr y, y⟩

/-- Exercise A.1.2 -/
example {X Y : Prop} : ¬(X ↔ Y) ↔ Xor' X Y := by
  unfold Xor'
  rewrite [iff_comm]
  rewrite [iff_not_comm]
  rewrite [not_or]
  simp only [not_and]
  simp only [not_not]
  constructor
  · intro h
    exact ⟨h.mp, h.mpr⟩
  intro h
  exact ⟨h.left, h.right⟩

/-- Exercise A.1.3 -/
def Exercise_A_1_3 : Decidable (∀ (X Y : Prop), (X → Y) → (¬X → ¬Y) → (X ↔ Y)) := by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`,
  -- depending on whether you believe the given statement to be true or false.
  apply isTrue
  intro X Y
  intro xy yx
  rewrite [not_imp_not] at yx
  exact ⟨xy, yx⟩

/-- Exercise A.1.4 -/
def Exercise_A_1_4 : Decidable (∀ (X Y : Prop), (X → Y) → (¬Y → ¬X) → (X ↔ Y)) := by
  apply isFalse
  rewrite [not_forall]
  use False
  rewrite [not_forall]
  use True
  rewrite [not_imp_not]
  rewrite [false_implies]
  simp only [true_implies]
  trivial

/-- Exercise A.1.5 -/
def Exercise_A_1_5 : Decidable (∀ (X Y Z : Prop), (X ↔ Y) → (Y ↔ Z) → [X, Y, Z].TFAE) := by
  apply isTrue
  intro X Y Z
  intro xy yz
  tfae_finish

/-- Exercise A.1.6. -/
def Exercise_A_1_6 : Decidable
    (∀ (X Y Z : Prop), (X → Y) → (Y → Z) → (Z → X) → [X, Y, Z].TFAE) := by
  apply isTrue
  intro X Y Z
  intro xy yz zx
  tfae_finish
