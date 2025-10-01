/-
In this section, we will learn how to prove theorem using some Basic
logic structure, starting from logical connectors and quantifiers.
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.StarOrdered
import Reap

/- The classical definitiion of limit in `ε-δ` language. -/
def epsilon_delta_limit (f : ℝ → ℝ) (l : ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - l| < ε

/- Infinite version of limit in `ε-δ` language -/
def epsilon_delta_limit_inf (f : ℝ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x > δ, |f x - l| < ε

/-
## Deal with connectors

- `x ∧ y` in goal: constructor or directly give ⟨x, y⟩
- `h : h₁ ∧ h₂` in the context: `h.left` to obtain h₁, `h.right` to obtain
`h₂`
- `x ∨ y` in goal: `left` or `right`
- `h : x ∨ y` in context: `cases' h with h₁ h₂`
-/
example : x < |y| → x < y ∨ x < -y := by
  intro a
  exact lt_abs.1 a

/-
## Deal with Universal Quatifier

### Usage of `intro` tactic
1. Implications `A → B`
2. Universal Quantifiers `∀ x, p x`
3. Deal with sets
-/
example (ε : ℝ) : ε > 0 → 1 / ε > 0 := by
  intro hε
  rw [gt_iff_lt] at hε ⊢ -- `rw` acts on `hε` and current goal, type \|-
  rw [one_div_pos]
  exact hε

example : ∀ x : ℝ, x > 0 → |x| = x := by
  intro x
  intro hx
  rw [abs_of_pos hx]

example (s : Set α) : s ⊆ s := by
  intro x xs
  exact xs

/- Notice that to prove this theorem, we are actually constructing a
function type. -/
example (ε : ℝ) : ε > 0 → 1 / ε > 0 := fun he => by
  rw [gt_iff_lt] at he ⊢
  rw [one_div_pos]
  exact he

/- This really shortens the proof! -/
example : ∀ x : ℝ, x > 0 → |x| = x := fun _ hx => abs_of_pos hx

/-
## Deal with Existence quantifier

Use `use y` tactic if you want to prove a prop of type `∃ x, ...`;
Use `rcases h with ⟨x, hx⟩` if you want to extract information from
`h : ∃ x, ...`
-/

example : ∃ δ : ℝ, δ < 1 := by
  use 0
  exact zero_lt_one

example : ∃ δ : ℝ, δ < 1 := ⟨0, zero_lt_one⟩

example (ε : ℝ) (hδ : ∃ δ > 0, δ < ε) : ∃ δ > 0, δ < ε / 2 := by
  rcases hδ with ⟨δ, hδ⟩
  use δ / 2
  constructor
  · simp [hδ.left]
  rw [div_lt_div_iff_of_pos_right]
  · exact hδ.right
  simp

/- The limit of `1/x` as `x` approaches ∞ is `0`. -/
theorem limit_of_one_div_x_eq_zero :
  epsilon_delta_limit_inf (fun x => 1 / x) 0 := by
  -- `dsimp` to definitively simp declarations (totally unnessary)
  dsimp [epsilon_delta_limit_inf]
  -- `intro` to introduce free vars in the universal quantifiers
  -- `intro` automatically match the free variables in order
  -- syntax of `∀ ε > 0,` is a short form of `∀ ε, ε > 0 →`,
  -- so we need to introduce both `ε : ℝ` and `hε : ε > 0`
  intro ε hε
  -- `use` to directly specify the var in the existence quantifier,
  -- `∃ δ > 0,` is a short form of `∃ δ, δ > 0 ∧`, so after specify
  -- the value of `δ`, we need to first prove `δ > 0`.
  use 1 / ε
  -- `constructor` to split the `∧` connector
  constructor
  -- `·` to focus on the main goal (unnessary, but for a neat proof)
  -- Here `simp` tactic uses a set of predefined lemmas to simplify
  -- the goal, type `simp?` to see the exact list of lemmas used.
  · simp [hε]
  -- `intro` works the same
  intro x hx
  -- Later we find that `x > 0` is needed for multiple times,
  -- so we can use `have` to prove this fact in the first place.
  have x_pos : x > 0 := by
    -- keyword `trans` represents the transitivity of an operation,
    -- here it means the transitivity of `>`. It works if you want
    -- to prove `a > b` by proving `a > c > b`.
    apply gt_trans hx
    simp [hε]
  simp only [sub_zero]
  -- Enter a `calc` mode to chain multiple inequalities
  calc
    _ = 1 / x := by
      rw [abs_of_pos]
      simp [x_pos]
    _ < ε := by
      -- `gt_iff_lt` means `a > b` is equivalent to `b < a`,
      -- you will need this very often.
      rw [gt_iff_lt] at hx
      -- It takes some time to get mul and div right ...
      rw [div_lt_iff₀ hε] at hx
      rw [mul_comm, ← div_lt_iff₀ x_pos] at hx
      exact hx

/- Use term trick to reduce the length -/
theorem limit_of_one_div_x_eq_zero' :
  epsilon_delta_limit_inf (fun x => 1 / x) 0 := fun ε hε =>
  ⟨1/ε, ⟨by simp [hε], fun x hx => by
    have x_pos : x > 0 := gt_trans hx (by simp [hε])
    rw [sub_zero, abs_of_pos (by simp [x_pos])]
    rw [gt_iff_lt, div_lt_iff₀ hε, mul_comm,
    ← div_lt_iff₀ x_pos] at hx
    exact hx⟩⟩

/- What if we want it to be more 'pretty'?
Use a pretty-printed `notation` -/
notation :max "lim " x:40 " → " c:10 ", " r:70 " = " "∞" =>
  epsilon_delta_limit_inf (fun x => r) c

/- Exactly same thing with above lemma. This mechanism turns out
to be the foundation for our `CalculusGame` project! -/
theorem pretty_limit_of_one_div_x_eq_zero :
  lim x → 0, x = ∞ := by
  dsimp [epsilon_delta_limit_inf]
  sorry

/- Your turn: show that lim x → 0, 2 * x = 0 -/
theorem limit_of_two_mul_x_eq_zero :
  epsilon_delta_limit (fun x => 2 * x) 0 0 := by
  sorry

/-
## Deal with Contraposition
Typical Bound definition you would expect -/
def HasUpperBound (f : ℝ → ℝ) : Prop := ∃ M : ℝ, ∀ x : ℝ, f x ≤ M

/- Use `contrapose!` to prove the contraposition of a problem.
Generally you if you want to prove `A → B`, you can prove `¬B → ¬A`
instead. -/
theorem id_no_upper_bound : ¬ HasUpperBound (fun x => x) := by
  dsimp [HasUpperBound]
  contrapose!
  intro h M
  use M + 1
  simp

/-
# Deal with Induction
Use `induction` tactic to prove theorems. -/

/- Last time we talked about we can construct most of the structures
(number field) on top of `ℕ`, so how is `ℕ` constructed? -/
#check ℕ

/- `ℕ` is defined as a inductive type, so we can use `induction` to
define functions (by matching) or to prove theorems about `ℕ`.
Here is how we define the factorial function.
-/
def fac : ℕ → ℕ
  -- fun n =>
  --   match n with
  --   | Nat.zero => 1
  --   | Nat.succ n => (n + 1) * fac n
  | 0 => 1
  | n + 1 => (n + 1) * fac n

theorem fac_pos (n : ℕ) : fac n > 0 := by
  induction n with
  | zero => dsimp [fac]; simp
  | succ hk hkk => dsimp [fac]; simp; exact hkk

theorem sum_of_id' (n : ℕ) : ∑ i ∈ Finset.range n, i = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k hk =>
  rw [Finset.sum_range_succ]
  rw [hk]
  rw [add_comm _ k, ← Nat.mul_add_div, mul_comm 2 k, ← left_distrib]
  rw [mul_comm k, Nat.add_sub_cancel]
  congr 1
  match k with
  | 0 => simp
  | k + 1 => simp [add_comm 2]
  simp

/- A much easier approach from Mathlib -/
theorem sum_id (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction n with
  | zero => simp
  | succ k hk =>
  rw [Finset.sum_range_succ, mul_add 2, ← hk]
  ring
