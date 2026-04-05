import Mathlib.Tactic

/-!
# Analysis I, Appendix A.2: Implication

An introduction to implications. Showcases some basic tactics and Lean syntax.

-/

example {X Y : Prop} (hX : X) : (X → Y) ↔ Y := ⟨λ xy ↦ xy hX, λ y _ ↦ y⟩

example {X Y : Prop} (hX': ¬X) : X → Y := by
  intro hX
  contradiction

example {X Y : Prop} (hXY : X → Y) (hX : X) : Y := by
  exact hXY hX

example {X Y : Prop} (hXY : X → Y) (hX : X) : Y := hXY hX

example {X Y : Prop} (hXY : X → Y) (h : ¬Y) : ¬X := by
  contrapose! h
  exact hXY h

theorem example_A_2_1 (x : ℤ) : x=2 → x^2=4 := by
  intro h
  rewrite [h]
  rfl

example : (2:ℤ)=2 → (2:ℤ)^2=4 := example_A_2_1 2

example : (3:ℤ)=2 → (3:ℤ)^2=4 := example_A_2_1 3

example : (-2:ℤ)=2 → (-2:ℤ)^2=4 := example_A_2_1 (-2)

#check Classical.not_imp

example : ¬(2+2=4 → 4+4=2) := by
  rewrite [Classical.not_imp]
  constructor
  · rfl
  norm_num

example {X Y : Prop} : X → Y ↔ Y ≥ X := by simp

example {X Y : Prop} : X → Y ↔ (¬X) ≥ ¬Y := by
  simp
  rewrite [not_imp_not]
  rfl

example {John_left_at_five John_here_now : Prop} (h1 : John_left_at_five → John_here_now)
    (h2 : ¬John_here_now) : ¬John_left_at_five := by
  contrapose! h2
  exact h1 h2

example {Washington_capital_US : Prop} (h : Washington_capital_US) :
    (1+1=2) → Washington_capital_US := λ _ ↦ h

example {NYC_capital_US : Prop} : 2+2=3 → NYC_capital_US := by
  norm_num1
  exact False.elim

/-- Proposition A.2.2 -/
example : (2+2:ℤ)=5 → 4=(10-4:ℤ) := by
  intro h
  have : (4 + 4:ℤ) = 10 := by
    replace h := congr(2*$h)
    convert h using 1
  rewrite [←eq_sub_iff_add_eq] at this
  exact this

/-- Theorem A.2.4 -/
theorem theorem_A_2_4 (n : ℤ) : Even (n * (n+1)) := by
  obtain heven | hodd := Int.even_or_odd n  -- or `rcases Int.even_or_odd with heven | hodd`
  · exact Even.mul_right heven _
  exact Even.mul_left (Odd.add_one hodd) _

/-- Corollary A.2.5 -/
example :
  let n : ℤ := (253+142)*123-(423+198)^342+538-213
  Even (n * (n+1)) := theorem_A_2_4 _

example : ∀ x : ℝ, x = 2 → x^2 = 4 := by
  intro x h
  rewrite [h]
  norm_num1

example : ¬∀ x : ℝ, x^2 = 4 → x = 2 := by
  rewrite [not_forall]
  use -2
  rewrite [Classical.not_imp]
  norm_num1
  exact ⟨True.intro, True.intro⟩

example {X Y : Prop} : (X ↔ Y) = ((X → Y) ∧ (Y → X)) := by
  rewrite [eq_iff_iff]
  exact ⟨λ iff ↦ ⟨iff.mp, iff.mpr⟩, λ and ↦ ⟨and.left, and.right⟩⟩

example (x : ℝ) : x=2 ↔ 2*x=4 := by
  constructor
  . intro h
    rewrite [h]
    norm_num1
  intro h
  linarith

example {X Y : Prop} : (X ↔ Y) = (X = Y) := by
  nth_rewrite 2 [eq_iff_iff]
  rfl

example : (3 = 2) → (6 = 4) := by
  norm_num1
  exact λ f ↦ f

example : ∃ (X Y : Prop), (X → Y) ≠ (Y → X) := by
  let x := -2
  use x = 2, x^2 = 4
  subst x
  norm_num1
  rewrite [ne_eq]
  rewrite [false_implies, true_implies]
  exact false_of_true_eq_false

theorem contrapositive {X Y : Prop} (hXY : X → Y) : ¬Y → ¬X := by
  intro nY hX
  have := hXY hX
  contradiction

theorem imp_example (x : ℝ) : x=2 → x^2=4 := by
  intro h
  rewrite [h]
  norm_num1

theorem imp_contrapositive (x : ℝ) : x^2≠4 → x≠2 := by
  exact contrapositive (imp_example x)

/-- Proposition A.2.6 -/
example {x : ℝ} (h : x>0) (hsin : Real.sin x = 1) : x ≥ Real.pi / 2 := by
  by_contra! h'
  have h1 : Real.sin x < Real.sin (Real.pi / 2) := by
  -- the <;> tactic applies the next tactic to all currently visible goals.
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two _ _ h' <;> linarith
  simp at h1
  linarith
