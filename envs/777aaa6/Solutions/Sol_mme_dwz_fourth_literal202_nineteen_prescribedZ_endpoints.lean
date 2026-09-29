-- Prove2me | solution 1 for mme_dwz_fourth_literal202_nineteen_prescribedZ_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T08:43:14.454239+00:00
-- url     : https://prove2.me/submissions/2c97e311-3818-4ea1-adf7-8181dd9344f5

import Definitions.Def_mme_dwz_fourth_literal202_row_data
import Theorems.Thm_mme_dwz_canonical202_prescribed_z_six_restriction_value_all_q
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Mathlib.Tactic

open BigOperators Module
open MME MME.DWZComponentRestriction MME.DWZRestrictedValue MME.DWZFineChannel

universe u
set_option autoImplicit false

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MME.ZEndpoint202PublicRows

def scale (q : ℚ) : ℕ :=
  ((List.range 12).find? fun k => 1 ≤ q * 2 ^ k).getD 0

def logParameter (q : ℚ) (k : ℕ) : ℚ :=
  (q * 2 ^ k - 1) / (q * 2 ^ k + 1)

def logPartial (q : ℚ) (k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range 10, logParameter q k ^ (2 * j + 1) / (2 * j + 1)

def logLower (q : ℚ) (k : ℕ) : ℚ :=
  2 * logPartial q k - k * (69314718057 / 100000000000 : ℚ)

def logUpper (q : ℚ) (k : ℕ) : ℚ :=
  2 * (logPartial q k + logParameter q k ^ 21 /
    (1 - logParameter q k ^ 2)) - k * (69314718055 / 100000000000 : ℚ)

theorem logInterval (q : ℚ) (k : ℕ) (hq : 0 < q)
    (hscale : 1 ≤ q * 2 ^ k) :
    (logLower q k : ℝ) ≤ Real.log (q : ℝ) ∧
      Real.log (q : ℝ) ≤ (logUpper q k : ℝ) := by
  let x : ℚ := q * 2 ^ k
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hscale
  have hxp : 0 < x + 1 := by linarith
  apply mme_log_interval_of_exact_rational_series_certificate
    q (logParameter q k) (logLower q k) (logUpper q k) k 10 hq
  · exact div_nonneg (sub_nonneg.mpr hscale) hxp.le
  · change (x - 1) / (x + 1) < 1
    rw [div_lt_one hxp]
    linarith
  · dsimp [logParameter, x]
    field_simp
    ring
  · simp [logLower, logPartial]
  · simp [logUpper, logPartial]

def entropyLower (i : Fin 19) : ℚ :=
  ∑ a : Fin 3, -(frequency i a * logUpper (frequency i a) (scale (frequency i a)))

def log5Lower : ℚ := logLower (5 / 4) 0 + 2 * logLower 2 0

def rateLower (i : Fin 19) : ℚ :=
  (790643 / 1000000) * (entropyLower i + 2 * frequency i 1 * log5Lower)

theorem frequencyCertificate (i : Fin 19) (a : Fin 3) :
    0 < frequency i a ∧ 1 ≤ frequency i a * 2 ^ scale (frequency i a) := by
  decide +kernel +revert

theorem rateCertificate (i : Fin 19) : (rows i).rate ≤ rateLower i := by
  decide +kernel +revert

theorem log5Lower_le : (log5Lower : ℝ) ≤ Real.log 5 := by
  have h5 := (logInterval (5 / 4) 0 (by norm_num) (by norm_num)).1
  have h2 := (logInterval 2 0 (by norm_num) (by norm_num)).1
  have heq : Real.log (5 : ℝ) =
      Real.log ((5 / 4 : ℚ) : ℝ) + 2 * Real.log 2 := by
    rw [show (5 : ℝ) = (((5 / 4 : ℚ) : ℝ) * 2 ^ 2) by norm_num,
      Real.log_mul (by norm_num : (((5 / 4 : ℚ) : ℝ) ≠ 0))
        (by norm_num : (2 : ℝ) ^ 2 ≠ 0), Real.log_pow]
    norm_num
  rw [heq]
  simpa [log5Lower] using add_le_add h5
    (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 2))

theorem entropyLower_le (i : Fin 19) :
    (entropyLower i : ℝ) ≤ ∑ a : Fin 3, Real.negMulLog (frequency i a : ℝ) := by
  unfold entropyLower
  push_cast
  apply Finset.sum_le_sum
  intro a _
  obtain ⟨hpos, hscale⟩ := frequencyCertificate i a
  have hlog := (logInterval (frequency i a) (scale (frequency i a)) hpos hscale).2
  rw [Real.negMulLog_eq_neg]
  apply neg_le_neg
  apply mul_le_mul_of_nonneg_left hlog
  exact_mod_cast hpos.le

theorem rate_le_publicLogRate (i : Fin 19) :
    ((rows i).rate : ℝ) ≤ (790643 / 1000000 : ℝ) *
      ((∑ a : Fin 3, Real.negMulLog (frequency i a : ℝ)) +
        2 * (frequency i 1 : ℝ) * Real.log 5) := by
  have hcert : ((rows i).rate : ℝ) ≤ (rateLower i : ℝ) := by
    exact_mod_cast rateCertificate i
  apply hcert.trans
  unfold rateLower
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add (entropyLower_le i)
  apply mul_le_mul_of_nonneg_left log5Lower_le
  apply mul_nonneg (by norm_num)
  exact_mod_cast (frequencyCertificate i 1).1.le

theorem endpoint_le_publicEndpoint (i : Fin 19) :
    Real.exp ((rows i).rate : ℝ) ≤
      Real.exp ((790643 / 1000000 : ℝ) *
        ∑ a : Fin 3, Real.negMulLog (((profile i).count a : ℝ) / (profile i).denominator)) *
      (5 : ℝ) ^ (2 * (790643 / 1000000 : ℝ) *
        ((profile i).count 1 : ℝ) / (profile i).denominator) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert rate_le_publicLogRate i using 1
  simp only [frequency, profile, Rat.cast_div, Rat.cast_natCast]
  ring


end MME.ZEndpoint202PublicRows

open MME.ZEndpoint202PublicRows

theorem solution (K : Type u) [Field K] (i : Fin 19) :
    let bZ : Basis (LiftedCoarsePair.{u} 5 2) K ((Central202Block K 5).V 2) :=
      (coarseClassBasis (K := K) 5 2 2).reindex Equiv.ulift.symm
    HasPrescribedZSixRestrictionValueAtLeast (Central202Block K 5) bZ
      LiftedCoarsePair.leftGrade (profile i) (790643 / 1000000 : ℝ)
      (Real.exp ((rows i).rate : ℝ)) := by
  have hpublic := mme_dwz_canonical202_prescribed_z_six_restriction_value_all_q
    K 5 (by norm_num) (profile i) (790643 / 1000000 : ℝ) (by norm_num)
  obtain ⟨_, hpublic⟩ := hpublic
  refine ⟨(Real.exp_pos _).le, ?_⟩
  intro v hv hlt cutoff
  exact hpublic v hv (hlt.trans_le (endpoint_le_publicEndpoint i)) cutoff
