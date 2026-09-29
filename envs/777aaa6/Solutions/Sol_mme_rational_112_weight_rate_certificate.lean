-- Prove2me | solution 1 for mme_rational_112_weight_rate_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:09:45.045898+00:00
-- url     : https://prove2.me/submissions/551211e0-f8a3-437a-a3cf-4b28397e26e3

import Theorems.Thm_mme_rational_entropy_log_bounds
import Theorems.Thm_mme_CW5_base_log_bounds

open scoped BigOperators
open MME.RegionRate

/-- Rational logarithm certificates bound the complete 112 entropy and
matrix-dimension rate before applying its physical scale and explicit loss. -/
theorem solution
    (p tau : ℚ) (hp : 0 ≤ p) (hpmax : p ≤ 1 / 2) (htau : 0 ≤ tau)
    (lower upper : Fin 3 → ℚ)
    (hlog : ∀ a, 0 < (![p, p, 1 - 2 * p] : Fin 3 → ℚ) a →
      (lower a : ℝ) ≤ Real.log (((![p, p, 1 - 2 * p] : Fin 3 → ℚ) a : ℚ) : ℝ) ∧
        Real.log (((![p, p, 1 - 2 * p] : Fin 3 → ℚ) a : ℚ) : ℝ) ≤ (upper a : ℝ))
    (bound : ℚ)
    (hcert : bound ≤
      4 * (-(∑ a, (![p, p, 1 - 2 * p] : Fin 3 → ℚ) a * upper a) +
        2 * (693147180559 / 1000000000000)) +
      24 * (1 - p) * tau * (1609437912434 / 1000000000000)) :
    (bound : ℝ) ≤
      4 * (entropy ![(p : ℝ), (p : ℝ), 1 - 2 * (p : ℝ)] + 2 * Real.log 2) +
      24 * (1 - (p : ℝ)) * (tau : ℝ) * Real.log 5 := by
  have hd : ∀ a, 0 ≤ (![p, p, 1 - 2 * p] : Fin 3 → ℚ) a := by
    intro a
    fin_cases a <;> simp <;> linarith
  have he := (mme_rational_entropy_log_bounds ![p, p, 1 - 2 * p] hd lower upper hlog).1
  have h2 := (mme_CW5_base_log_bounds 0).1
  have h5 := (mme_CW5_base_log_bounds 1).1
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Rat.cast_ofNat,
    Rat.cast_div] at h2 h5
  have hpR := (Rat.cast_le (K := ℝ)).2 hpmax
  norm_num at hpR
  have htR : 0 ≤ (tau : ℝ) := by exact_mod_cast htau
  have hcoef : 0 ≤ 24 * (1 - (p : ℝ)) * (tau : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) htR
  have hm := mul_le_mul_of_nonneg_left h5 hcoef
  have hc := (Rat.cast_le (K := ℝ)).2 hcert
  push_cast at he hc
  have hv : (fun a ↦ ((![p, p, 1 - 2 * p] : Fin 3 → ℚ) a : ℝ)) =
      ![(p : ℝ), (p : ℝ), 1 - 2 * (p : ℝ)] := by
    funext a
    fin_cases a <;> simp
  rw [hv] at he
  linarith


#print axioms solution
