import Mathlib
import Reap

class ArithProg (a : ℕ → α) [AddCommGroup α] where
  equal_diff : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n

namespace ArithProg

variable {α : Type} [AddCommGroup α]
variable {a : ℕ → α} [inst : ArithProg a]

local notation "d" => a 1 - a 0

theorem comm_diff : ∀ n, a (n + 1) - a n = d := by
  intro n
  induction' n with k hk
  · simp
  rw [← hk]
  exact inst.equal_diff k

theorem formula : ∀ n, a n = a 0 + n • d := by
  intro n
  induction' n with k hk
  · simp
  rw [add_smul, ← add_assoc, ← hk, one_smul]
  rw [← comm_diff k]
  abel

local notation "S" n:max => ∑ i ∈ Finset.range n, a i

theorem sum_formula : ∀ n, S n = n • a 0 + (n * (n - 1) / 2) • d := by
  intro n
  induction' n with k hk
  · simp
  rw [Finset.sum_range_succ, hk]
  rw [formula (a := a) k]
  sorry

end ArithProg

open ArithProg

def b (n : ℕ) : ℝ := n

instance : ArithProg b where
  equal_diff n := by simp [b]; norm_num

#check formula (a := b)
#check sum_formula (a := b)
