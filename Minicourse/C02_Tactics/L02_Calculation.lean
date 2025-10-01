/-
# Basic Calculation in Field of Real Number

In this file, we will expand on several basic topics
to make it easier to prove by calculation.

1. Basic tactics `rw`, `rfl`, `apply`, `exact`
2. Use of `calc` block
3. Simple rule-based simplifiers `group`, `ring`,
   and `field_simp`

Main goal in this file is to prove the `gaokao_triangle` theorem
Given cos(α+β)=m, tan(α)tan(β)=2, show that cos(α-β)=-3m
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Reap

open Real

/- Directly give the type of the proof -/
example (a : ℝ) : a = a := rfl

/- Directly give the type of the proof -/
example (a b c : ℝ) : a * b * c = a * (b * c) :=
  mul_assoc a b c

/- Construct the proof once is efficient, but is ugly
and non-human -/
example (a b c : ℝ) : a * b * c = b * c * a :=
  (mul_assoc a b c).trans (mul_comm a (b * c))

/- Most of time it is challenging to directy give the proof,
so we choose to prove it interactively and step-by-step.
The keyword `by` will allow you enter tactic mode.
`exact` is a simple tactic that finishes the proof.
-/
example (a b c : ℝ) : a * b * c = a * (b * c) := by
  exact mul_assoc a b c

example (a : ℝ) : a = a := by
  rfl

/- We can also use the `rewrite` tactic to rewrite the goal
You can rewrite either iff statements or equalities.
 -/
example (a b c : ℝ) : a * b * c = b * c * a := by
  rewrite [mul_assoc]
  rewrite [mul_comm]
  exact rfl -- rfl is a tactic that shows `x = x`, a reflexive proof

/- TODEMO -/
/- `rw` is a tactic combining `rewrite` and `rfl`, it tries to
apply `rfl` immediately after `rewrite` -/
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]
  -- rw [mul_comm, mul_assoc]

/- Use fact from local contexts `h` `h'` -/
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

/- Explore some properties for ℝ. Properties of a type is expressed
by an `instance`, we will explain this in later lectures. -/
#check ℝ
#synth AddCommGroup ℝ
#synth CommRing ℝ
#synth Field ℝ
#synth GroupWithZero ℝ
-- #synth LinearOrderedField ℝ

/- Explore some lemmas about relations/orders -/
#check rfl
#check symm
#check trans
#check le_trans
#check Eq.trans
#check le_antisymm -- more relations


/- TODEMO -/
/- A `calc` block allows you to proof an equality
or inequality step by step. -/
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a*a)]
    _ = _ := by
    -- use `_ = _ := by` to let Lean deduce the goal
      rw [mul_comm b a, ← two_mul]

/- `ring` is a tactic that can solve equations within commutative rings
ℝ is a ring. -/
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

/- A more complex one with mul and div -/
example (a b c d : ℝ) : (a / b) * (c / d) = (a * c) / (b * d) := by
  rw [mul_comm_div, div_div, mul_div, mul_comm d]
  -- ring

-- #leansearch "Real.tan is equal to sin div by cos"
#check tan_eq_sin_div_cos

/- TODO -/
lemma tan_mul_eq_sin_mul_div_cos_mul {α β : ℝ} :
  tan α * tan β = (sin α * sin β) / (cos α * cos β) := by
  calc
      tan α * tan β = (sin α / cos α) * (sin β / cos β) := by
        rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
      _ = (sin α * sin β) / (cos α * cos β) := by
        rw [mul_comm_div, div_div, mul_div, mul_comm (cos α)]

/- TODEMO -/
/- To prepare us for the main theorem, we need to show an obvious
but nontrivial lemma.
In ℝ, for arbituary `a`, if `b = 0`, then `a / b = 0`. This is
because a / b = a * b⁻¹ and 0⁻¹ is defined to be 0. -/
#check div_ne_zero_iff
#check div_eq_zero_iff

lemma div_eq_of_eq_mul₀ {a b c : ℝ} (h : c ≠ 0) :
  a / b = c → a = c * b := by
  intro h₁
  rw [← h₁] at h
  rw [div_ne_zero_iff] at h
  have := h.right
  rw [div_eq_iff this] at h₁
  exact h₁

/- `field_simp` is a carefully crafted tactic to solve problem on field. -/
lemma div_eq_of_eq_mul₀' {a b c : ℝ} (h : b ≠ 0) : a / b = c → a = c * b := by
  intro h₁
  -- rw [div_eq_iff h] at h₁
  field_simp at h₁
  linear_combination h₁

#leansearch "cos (a+b)"
-- #leansearch "cos (a-b)"

-- #herald "Real if a / b = c then a = b * c."
/-- 2024 Gaokao Xinkebiao I - 4:  -/
theorem gaokao_triangle (α β m : ℝ) (h₁ : cos (α + β) = m) (h₂ : tan α * tan β = 2) :
  cos (α - β) = -3 * m := by
  /- We can use a `have` block to prove some lemmas -/
  have : sin α * sin β = 2 * cos α * cos β := by
    sorry
  sorry

section Exercise

example : cos (2 * θ) = 2 * (cos θ) ^ 2 - 1 := sorry

/- Given sin(α-β)=1/3, cos(α) sin(β)=1/6, show that cos(2α+2β)=1/9. -/
example : sorry := sorry

/- Show that cosα - cosβ = 2 sin((α+β)/2) sin((β-α)/2) -/
example : sorry := sorry

end Exercise
