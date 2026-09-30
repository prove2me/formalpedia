-- Prove2me | solution 1 for log2_log3_irrational
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:03:56.619513+00:00
-- url     : https://prove2.me/submissions/a770fcc8-382d-4b1f-8863-a9c6022a899e

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false

theorem solution : Irrational (Real.log 2 / Real.log 3) := by
  rintro ⟨q, hq⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hqpos : 0 < (q : ℝ) := by rw [hq]; exact div_pos hlog2 hlog3
  have hnum : 0 ≤ q.num := le_of_lt (Rat.num_pos.mpr (by exact_mod_cast hqpos))
  have hcast : (q.num.toNat : ℝ) = (q.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hcross : (q.den : ℝ) * Real.log 2 = (q.num : ℝ) * Real.log 3 := by
    rw [Rat.cast_def] at hq
    have h := (div_eq_div_iff hden (ne_of_gt hlog3)).mp hq
    nlinarith
  have hpowers : (2 : ℝ) ^ q.den = (3 : ℝ) ^ q.num.toNat := by
    apply Real.log_injOn_pos
      (show 0 < (2 : ℝ) ^ q.den by positivity)
      (show 0 < (3 : ℝ) ^ q.num.toNat by positivity)
    simpa only [Real.log_pow, hcast] using hcross
  have hpowers_nat : (2 : ℕ) ^ q.den = 3 ^ q.num.toNat := by exact_mod_cast hpowers
  have heven : 2 ∣ (2 : ℕ) ^ q.den := dvd_pow_self 2 q.den_nz
  rw [hpowers_nat] at heven
  have : (2 : ℕ) ∣ 3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two heven
  norm_num at this

#print axioms solution
