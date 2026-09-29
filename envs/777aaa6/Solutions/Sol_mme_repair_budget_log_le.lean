-- Prove2me | solution 1 for mme_repair_budget_log_le
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T14:02:12.768073+00:00
-- url     : https://prove2.me/submissions/65c30405-a9e6-4c74-b3cc-b9c7ace384cd

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-- The repair budget has logarithmic cost controlled by the capacity,
with the base-change factor exposed for choosing the repair scale. -/
theorem solution (d C : ℕ) :
    Real.log ((8 : ℝ) ^ (Nat.log d C + 1)) ≤
      Real.log 8 + (Real.log 8 / Real.log d) * Real.log C := by
  have h := Real.natLog_le_logb C d
  have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_right h h8
  rw [Real.log_pow]
  simp only [Real.logb, Nat.cast_add, Nat.cast_one] at hm ⊢
  convert add_le_add_right hm (Real.log 8) using 1 <;> ring

/-- One repair scale makes its logarithmic cost an arbitrarily small
fraction of log capacity, uniformly over every natural capacity. -/
private theorem mme_repair_scale_exists_uniform_log_loss (delta : ℝ) (hdelta : 0 < delta) :
    ∃ d : ℕ, 1 < d ∧ ∀ C : ℕ,
      Real.log ((8 : ℝ) ^ (Nat.log d C + 1)) ≤ Real.log 8 + delta * Real.log C := by
  obtain ⟨s, hs⟩ := exists_nat_gt (1 / delta)
  let d := 8 ^ (s + 1)
  have hd : 1 < d := by
    dsimp [d]
    rw [pow_succ]
    have hp : 0 < 8 ^ s := pow_pos (by decide) _
    omega
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hlogd : Real.log (d : ℝ) = ((s : ℝ) + 1) * Real.log 8 := by
    simp [d, Nat.cast_pow, Real.log_pow]
  have hs' : 1 < (s : ℝ) * delta := (div_lt_iff₀ hdelta).mp hs
  have hratio : Real.log 8 / Real.log d ≤ delta := by
    apply (div_le_iff₀ (Real.log_pos hdR)).mpr
    rw [hlogd]
    nlinarith
  refine ⟨d, hd, fun C => (solution d C).trans ?_⟩
  exact add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_right hratio (Real.log_natCast_nonneg C))


#print axioms solution
