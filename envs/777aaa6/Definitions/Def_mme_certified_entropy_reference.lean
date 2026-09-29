-- Prove2me | Definitions.Def_mme_certified_entropy_reference
-- name    : mme_certified_entropy_reference
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-22T20:44:04.02819+00:00
-- url     : https://prove2.me/theorems/3816d4ac-83c7-4620-ad0f-867d1fe1497a
-- title:
--   Smooth reference values for certified entropy bounds
-- statement:
--   A reference value of the form 2^a 3^b 5^c 7^d, used as the comparison point in the Gibbs bound on an entropy term, together with its positivity and the expansion of its logarithm as an integer combination of log 2, log 3, log 5 and log 7.
-- source:
--   Certified evaluation of the entropy rates of the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6).

import Mathlib
import Definitions.Def_mme_regional_split_entropy_data

open BigOperators MME MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MME.Cert

/-- A reference value `2^a 3^b 5^c 7^d`, whose logarithm is an integer combination of four
logarithms. -/
noncomputable def qval (e : Fin 4 → ℤ) : ℝ := 2 ^ (e 0) * 3 ^ (e 1) * 5 ^ (e 2) * 7 ^ (e 3)

theorem qval_pos (e : Fin 4 → ℤ) : 0 < qval e := by
  unfold qval
  have h2 : (0 : ℝ) < 2 ^ (e 0) := zpow_pos (by norm_num) _
  have h3 : (0 : ℝ) < 3 ^ (e 1) := zpow_pos (by norm_num) _
  have h5 : (0 : ℝ) < 5 ^ (e 2) := zpow_pos (by norm_num) _
  have h7 : (0 : ℝ) < 7 ^ (e 3) := zpow_pos (by norm_num) _
  positivity

theorem log_qval (e : Fin 4 → ℤ) :
    Real.log (qval e) = (e 0 : ℝ) * Real.log 2 + (e 1 : ℝ) * Real.log 3 +
      (e 2 : ℝ) * Real.log 5 + (e 3 : ℝ) * Real.log 7 := by
  unfold qval
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_zpow, Real.log_zpow, Real.log_zpow,
    Real.log_zpow]

/-- `-p log p ≥ p - p²/q - p log q`: the Gibbs bound against an arbitrary positive reference. -/
theorem negMulLog_ge {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p - p ^ 2 / q - p * Real.log q ≤ Real.negMulLog p := by
  rcases hp.eq_or_lt with h | hp'
  · simp [← h, Real.negMulLog]
  · have hlog : Real.log (p / q) ≤ p / q - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hmul : p * Real.log (p / q) ≤ p * (p / q - 1) := by
      exact mul_le_mul_of_nonneg_left hlog hp
    rw [Real.log_div hp'.ne' hq.ne'] at hmul
    have hsq : p * (p / q) = p ^ 2 / q := by field_simp
    simp only [Real.negMulLog]
    nlinarith [hmul]

/-- `-p log p ≤ q - p - p log q`. -/
theorem negMulLog_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    Real.negMulLog p ≤ q - p - p * Real.log q := by
  rcases hp.eq_or_lt with h | hp'
  · simp [← h, Real.negMulLog]; positivity
  · have hlog : Real.log (q / p) ≤ q / p - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hmul : p * Real.log (q / p) ≤ p * (q / p - 1) := mul_le_mul_of_nonneg_left hlog hp
    rw [Real.log_div hq.ne' hp'.ne'] at hmul
    have hqp : p * (q / p) = q := by field_simp
    simp only [Real.negMulLog]
    nlinarith [hmul]

end MME.Cert


