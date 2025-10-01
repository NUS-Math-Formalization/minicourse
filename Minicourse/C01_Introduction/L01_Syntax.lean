import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Trigonometric
-- import ReaperTac

open Nat
/-
# Dependent Type theory

A framework for formalizing mathematics and logic reasoning.
It is based on the idea that each value has a type.
alpha.reaslab.io
live.lean-lang.org

-/

/-
## Type and Value
To display the type of your expression, use `#check`.
To evaluate your expression, use `#eval`
When you input the value of an expression, Lean will try
to infer the type of the value.
-/
#check 2 + 2
#check 2 + 2.0
#eval 2 + 2

#check 2 / 3
#eval  2 / 3
#check 2 - 3
#eval  2 - 3

/- You can also explicitly declare the type of your value. -/
#check (2 : ℚ)
#eval  (2 / 3 : ℚ)
#eval  (2 - 3 : ℚ)
#eval  (2 - 3 : ℤ)

/- To formally define a variable, we use `def`. -/
def a : ℕ := 2
def b : ℕ := 3

/- Use existing types to construct new types. -/
#check List
#check List ℕ
#check Finset ℕ
#check Set ℕ
#check ℕ → ℝ
#check ℝ × ℝ

/- Some types are representable, then you can show them. But some are not. -/
def finset_A : Finset ℕ := {1, 2}
def finset_B : Finset ℕ := {2, 3}
def set_A : Set ℕ := {1, 2}
def set_B : Set ℕ := {2, 3}
#check set_A ∪ set_B
#check set_A ∩ set_B
-- #eval finset_A ∪ finset_B
def list_two : List ℕ := [1, 2]
#eval list_two
-- #eval set_two -- This will not work.

/- Define a function on natural number, it can also be interpreted
as a series. -/
def ai : ℕ → ℕ :=
  fun x => 1 / (x + 3)

/- A more common way is to use `()` to specify the parameter -/
def f (x : ℕ) : ℕ :=
  x + 3

/- You can also define a function on real line -/
def f_real (x : ℝ) :=
  x + 3

#check f
#check f_real

/-
## Propositions and Proofs
The most important type in Lean is the Proposition type, which constructs theorems.
A proof of a proposition is a value of that type. -/

/- This is a very simple proposition. -/
def easy_prop : Prop :=
  2 + 2 = 4

/- We can use quantifiers to define more -/
def medium_prop : Prop :=
  ∀ x : ℝ, -5 < x ^ 3 ∧ x ^ 3 < 5

/- The classical definitiion of limit in `ε-δ` language. -/
def epsilon_delta_limit (f : ℝ → ℝ) (l : ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - l| < ε

#check epsilon_delta_limit

/- These are proofs of propositions. -/
theorem easy : easy_prop := rfl

/- Note that the type of `easy` is `2 + 2 = 4`. Its value is `rfl`,
which is a proof of the proposition. In general, if you provide a value
of type `p`, then you prove `p` -/
#check easy_prop
#check easy



/- Construct more complex object using proposition -/
def set_test : Set ℝ := {x | -5 < x ^ 3 ∧ x ^ 3 < 5}

/-
## Construct a mathematical statement
Use `def` to define an expression, whose type is a proposition.
This theorem shows the limit of the function `f_real` at `3` is `6`
-/
def epsilon_delta_limit_of_f_real :
  epsilon_delta_limit f_real 3 6 := sorry

#check epsilon_delta_limit_of_f_real

/- Moreover, you can put variables and propositions as params -/
def epsilon_delta_limit_of_f_real' (f : ℝ → ℝ) (a : ℝ) :
  ∃ l, ∀ ε > 0, ∃ δ > 0, ∀ x,
  0 < |x - a| ∧ |x - a| < δ → |f x - l| < ε := sorry

#check epsilon_delta_limit_of_f_real'

/- Here are some proofs from MIL -/
example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say `m` and `n` are natural numbers, and assume `n = 2 * k`.
  rintro m n ⟨k, hk⟩
  -- We need to prove `m * n` is twice a natural number. Let's show it's twice `m * k`.
  use m * k
  -- Substitute for `n`,
  rw [hk]
  -- and now it's obvious.
  ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]


/--
## Formalize a statement
2024 Gaokao Xinkebiao I - 1:
Suppose $A= {x | -5 < x^3 < 5}$, $B = {-3, -1, 0, 2, 3}$, find $A U B.
Answer is ${-1, 0}$ -/
def set_example (A B : Set ℝ) (h₁ : A = {x | -5 < x ^ 3 ∧ x ^ 3 < 5})
  (h₂ : B = {-3, -1, 0, 2, 3}) : A ∩ B = {-1, 0} := by
  sorry


/- 2024 Gaokao Xinkebiao I - 4
Given cos(α+β)=m, tan(α)tan(β)=2, show that cos(α-β)=-3m -/
open BigOperators Real Nat Topology
theorem cos_sub_cos_of_cos_add_cos
(m : ℝ) (α β : ℝ)
(h₁ : m = cos (α + β))
(h₂ : tan α * tan β = 2) :
cos (α - β) = -3 * m :=  by sorry

open BigOperators Real Nat Topology
theorem cos_sub_of_cos_add_eq_m {α β : ℝ} (m : ℝ) (h : Real.cos (α + β) = m) (h' : Real.tan α * Real.tan β = 2) : Real.cos (α - β) = -3 * m :=  by sorry
