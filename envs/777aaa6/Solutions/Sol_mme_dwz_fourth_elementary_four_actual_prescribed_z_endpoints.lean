-- Prove2me | solution 1 for mme_dwz_fourth_elementary_four_actual_prescribed_z_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T09:42:04.943996+00:00
-- url     : https://prove2.me/submissions/76d73603-8cf3-4bd9-8051-ad20f5e5b1fb

import Theorems.Thm_mme_dwz_q5_rectangular_four_prescribed_z_six_restriction_value
import Definitions.Def_mme_dwz_fourth_elementary_four_row_data
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Exact raw-profile rate certificates for the four residual elementary
square rows. The zero forbidden-grade frequency is handled separately. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open BigOperators MME.DWZRestrictedValue

namespace MME.ElementaryFourScalar

def scale (q : ℚ) : ℕ :=
  ((List.range 4).find? fun k => 1 ≤ q * 2 ^ k).getD 0

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



def entropyLower (i : Fin 4) : ℚ :=
  ∑ a : Fin 3, -(frequency i a * logUpper (frequency i a) (scale (frequency i a)))

def log5Lower : ℚ := logLower (5 / 4) 0 + 2 * logLower 2 0

def rateLower (i : Fin 4) : ℚ := tau * (entropyLower i + log5Lower)

theorem frequencyCertificate (i : Fin 4) (a : Fin 3) :
    frequency i a = 0 ∨
      (0 < frequency i a ∧ 1 ≤ frequency i a * 2 ^ scale (frequency i a)) := by
  decide +kernel +revert

theorem rateCertificate (i : Fin 4) : rate ≤ rateLower i := by
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


theorem entropyLower_le (i : Fin 4) :
    (entropyLower i : ℝ) ≤ ∑ a : Fin 3, Real.negMulLog (frequency i a : ℝ) := by
  unfold entropyLower
  push_cast
  apply Finset.sum_le_sum
  intro a _
  rcases frequencyCertificate i a with hzero | ⟨hpos, hscale⟩
  · simp [hzero]
  · have hlog := (logInterval (frequency i a) (scale (frequency i a)) hpos hscale).2
    rw [Real.negMulLog_eq_neg]
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_left hlog
    exact_mod_cast hpos.le

theorem rate_le_publicLogRate (i : Fin 4) :
    (rate : ℝ) ≤ (tau : ℝ) *
      ((∑ a : Fin 3, Real.negMulLog (frequency i a : ℝ)) + Real.log 5) := by
  have hcert : (rate : ℝ) ≤ (rateLower i : ℝ) := by
    exact_mod_cast rateCertificate i
  apply hcert.trans
  unfold rateLower
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by norm_num [tau])
  exact add_le_add (entropyLower_le i) log5Lower_le

theorem rate_le_counts (i : Fin 4) :
    (1820522261843 / 1000000000000 : ℝ) ≤ (790643 / 1000000 : ℝ) *
      ((∑ a : Fin 3, Real.negMulLog
        (((profile i).count a : ℝ) / (profile i).denominator)) + Real.log 5) := by
  simpa only [rate, tau, frequency, profile, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_ofNat] using rate_le_publicLogRate i

theorem endpoint_le_publicEndpoint (i : Fin 4) :
    Real.exp (1820522261843 / 1000000000000 : ℝ) ≤
      Real.exp ((790643 / 1000000 : ℝ) *
        ∑ a : Fin 3, Real.negMulLog
          (((profile i).count a : ℝ) / (profile i).denominator)) *
      (5 : ℝ) ^ (790643 / 1000000 : ℝ) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  convert rate_le_counts i using 1
  ring

end MME.ElementaryFourScalar



open MME MME.DWZComponentRestriction MME.DWZRestrictedValue Module
universe u

private theorem lowerEndpoint
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Type u} (bZ : Basis I K (T.V 2)) (grade : I → Fin 3)
    (p : IntegerZSplitProfile 3) (tau V W : ℝ)
    (hV : HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau V)
    (hW : 0 ≤ W) (hWV : W ≤ V) :
    HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau W :=
  ⟨hW, fun v hv hlt cutoff ↦ hV.2 v hv (hlt.trans_le hWV) cutoff⟩

theorem solution (K : Type u) [Field K] :
    HasPrescribedZSixRestrictionValueAtLeast
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 1 3))
      ((coarseClassBasis (K := K) 5 2 3).reindex Equiv.ulift.symm)
      LiftedCoarsePair.leftGrade (MME.ElementaryFourScalar.profile 0)
      (790643 / 1000000 : ℝ) (Real.exp (1820522261843 / 1000000000000 : ℝ)) ∧
    HasPrescribedZSixRestrictionValueAtLeast
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 3 0 1))
      ((coarseClassBasis (K := K) 5 2 1).reindex Equiv.ulift.symm)
      LiftedCoarsePair.leftGrade (MME.ElementaryFourScalar.profile 1)
      (790643 / 1000000 : ℝ) (Real.exp (1820522261843 / 1000000000000 : ℝ)) ∧
    HasPrescribedZSixRestrictionValueAtLeast
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 0 3 1))
      ((coarseClassBasis (K := K) 5 2 1).reindex Equiv.ulift.symm)
      LiftedCoarsePair.leftGrade (MME.ElementaryFourScalar.profile 2)
      (790643 / 1000000 : ℝ) (Real.exp (1820522261843 / 1000000000000 : ℝ)) ∧
    HasPrescribedZSixRestrictionValueAtLeast
      ((cwSquareCanonicalGrading K 5).blockSubtensor (cwSquareBlockType 1 0 3))
      ((coarseClassBasis (K := K) 5 2 3).reindex Equiv.ulift.symm)
      LiftedCoarsePair.leftGrade (MME.ElementaryFourScalar.profile 3)
      (790643 / 1000000 : ℝ) (Real.exp (1820522261843 / 1000000000000 : ℝ)) := by
  have htau : (0 : ℝ) < 790643 / 1000000 := by norm_num
  have h0 := (mme_dwz_q5_rectangular_four_prescribed_z_six_restriction_value
    K (MME.ElementaryFourScalar.profile 0) _ htau).1 (by decide +kernel)
  have h1 := (mme_dwz_q5_rectangular_four_prescribed_z_six_restriction_value
    K (MME.ElementaryFourScalar.profile 1) _ htau).2.2.2 (by decide +kernel)
  have h2 := (mme_dwz_q5_rectangular_four_prescribed_z_six_restriction_value
    K (MME.ElementaryFourScalar.profile 2) _ htau).2.1 (by decide +kernel)
  have h3 := (mme_dwz_q5_rectangular_four_prescribed_z_six_restriction_value
    K (MME.ElementaryFourScalar.profile 3) _ htau).2.2.1 (by decide +kernel)
  exact ⟨lowerEndpoint _ _ _ _ _ _ _ h0 (Real.exp_pos _).le
      (MME.ElementaryFourScalar.endpoint_le_publicEndpoint 0),
    lowerEndpoint _ _ _ _ _ _ _ h1 (Real.exp_pos _).le
      (MME.ElementaryFourScalar.endpoint_le_publicEndpoint 1),
    lowerEndpoint _ _ _ _ _ _ _ h2 (Real.exp_pos _).le
      (MME.ElementaryFourScalar.endpoint_le_publicEndpoint 2),
    lowerEndpoint _ _ _ _ _ _ _ h3 (Real.exp_pos _).le
      (MME.ElementaryFourScalar.endpoint_le_publicEndpoint 3)⟩

