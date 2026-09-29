-- Prove2me | solution 1 for mme_dwz_fourth_coupled63_prescribedZ_six_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T08:33:39.08105+00:00
-- url     : https://prove2.me/submissions/32a92418-f479-4724-bc4e-0ace4f3235f3

import Definitions.Def_mme_dwz_fourth_coupled63_canonical_row_data
import Theorems.Thm_mme_complete_split_112_prescribedZ_six_value
import Theorems.Thm_mme_complete_split_112_cyclic_prescribedZ_six_value
import Theorems.Thm_mme_log_interval_of_exact_rational_series_certificate
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Exact scalar alignment of the 63 canonicalized coupled rows of the q=5
fourth-power ledger. This certificate proves rate inequalities only; it does
not assert a tensor realization or compatibility of changed child profiles. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open BigOperators

namespace MME.Coupled63Scalar

def scale (q : ℚ) : ℕ :=
  ((List.range 20).find? fun k => 1 ≤ q * 2 ^ k).getD 0

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


def entropyLower (i : Fin 63) : ℚ :=
  ∑ a : Fin 3, -(frequency i a * logUpper (frequency i a) (scale (frequency i a)))

def log5Lower : ℚ := logLower (5 / 4) 0 + 2 * logLower 2 0

def rateLower (i : Fin 63) : ℚ :=
  (entropyLower i + 2 * logLower 2 0) / 3 +
    (790643 / 1000000) * logCoefficient i * log5Lower

theorem parameterCertificate (i : Fin 63) :
    0 < (rows i).l ∧ 0 < (rows i).g ∧ 341 * (rows i).l < 100 * (rows i).g ∧
    0 ≤ logCoefficient i := by
  decide +kernel +revert

theorem frequencyCertificate (i : Fin 63) (a : Fin 3) :
    0 < frequency i a ∧ 1 ≤ frequency i a * 2 ^ scale (frequency i a) := by
  decide +kernel +revert

theorem rateCertificate (i : Fin 63) : (rows i).rate ≤ rateLower i := by
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

theorem entropyLower_le (i : Fin 63) :
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


/-- Every stored log-rate is below the full unrotated/cyclic prescribed-Z
endpoint evaluated at its exact canonicalized integer parameters. -/
theorem rate_le_publicLogRate (i : Fin 63) :
    ((rows i).rate : ℝ) ≤
      ((∑ a : Fin 3, Real.negMulLog (frequency i a : ℝ)) + 2 * Real.log 2) / 3 +
        (790643 / 1000000 : ℝ) * (logCoefficient i : ℝ) * Real.log 5 := by
  have hcert : ((rows i).rate : ℝ) ≤ (rateLower i : ℝ) := by
    exact_mod_cast rateCertificate i
  apply hcert.trans
  unfold rateLower
  push_cast
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ (by norm_num)
    apply add_le_add (entropyLower_le i)
    exact mul_le_mul_of_nonneg_left
      (logInterval 2 0 (by norm_num) (by norm_num)).1 (by norm_num)
  · apply mul_le_mul_of_nonneg_left log5Lower_le
    apply mul_nonneg (by norm_num)
    exact_mod_cast (parameterCertificate i).2.2.2




open Module MME.CompleteSplit MME.CompleteSplit112
open MME.DWZRestrictedValue
universe u

theorem rho_matches_address (i : Fin 63) (mode : Fin 3) :
    (rho i mode).val = (rows i).address mode := by
  decide +kernel +revert

theorem rho_cases (i : Fin 63) :
    rho i = cwSquareBlockType 1 1 2 ∨
      rho i = (fun a => cwSquareBlockType 1 1 2 (cyclicPerm.symm a)) ∨
      rho i = (fun a => cwSquareBlockType 1 1 2 ((cyclicPerm.trans cyclicPerm).symm a)) := by
  decide +kernel +revert

theorem profile_count_unrotated (i : Fin 63) (h : rho i = cwSquareBlockType 1 1 2) :
    (profile i).count = ![(rows i).l, 2 * (rows i).g, (rows i).l] := by
  decide +kernel +revert

theorem profile_count_rotated (i : Fin 63) (h : rho i ≠ cwSquareBlockType 1 1 2) :
    (profile i).count =
      ![(rows i).l + (rows i).g, (rows i).l + (rows i).g, 0] := by
  decide +kernel +revert

theorem profile_entropy (p : ℚ) :
    (∑ w : Fin 2 → Fin 3, Real.negMulLog (profileProbability p 2 w : ℝ)) =
      Real.negMulLog (p : ℝ) + Real.negMulLog (1 - 2 * (p : ℝ)) +
        Real.negMulLog (p : ℝ) := by
  rw [← (finTwoArrowEquiv (Fin 3)).symm.sum_comp]
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, profileProbability,
    finTwoArrowEquiv]

theorem beta_entropy (i : Fin 63) (beta : Fin 3 → Profile 2)
    (hbeta : ∀ mode sigma, (beta mode).probability sigma =
      (profileProbability (((rows i).l : ℚ) /
        (2 * (((rows i).l + (rows i).g : ℕ) : ℚ))) mode sigma : ℝ)) :
    Real.log 2 * mme_modern_entropyBits (beta 2).probability =
      ∑ a : Fin 3, Real.negMulLog (frequency i a : ℝ) := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold mme_modern_entropyBits
  rw [mul_div_cancel₀ _ hlog]
  simp_rw [hbeta]
  change (∑ w : Fin 2 → Fin 3, Real.negMulLog
    (profileProbability (((rows i).l : ℚ) /
      (2 * (((rows i).l + (rows i).g : ℕ) : ℚ))) 2 w : ℝ)) = _
  rw [profile_entropy]
  have hlg : (0 : ℝ) < ((rows i).l : ℝ) + (rows i).g := by
    have hp := (parameterCertificate i).1
    have hpR : (0 : ℝ) < ((rows i).l : ℝ) := by exact_mod_cast hp
    positivity
  have hm : (1 : ℝ) - 2 * (((rows i).l : ℝ) /
      (2 * (((rows i).l : ℝ) + (rows i).g))) =
      2 * ((rows i).g : ℝ) / (2 * (((rows i).l : ℝ) + (rows i).g)) := by
    field_simp
    ring
  simp only [frequency, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_add, Nat.cast_add]
  rw [hm]
  rfl

theorem rate_le_betaRate (i : Fin 63) (beta : Fin 3 → Profile 2)
    (hbeta : ∀ mode sigma, (beta mode).probability sigma =
      (profileProbability (((rows i).l : ℚ) /
        (2 * (((rows i).l + (rows i).g : ℕ) : ℚ))) mode sigma : ℝ)) :
    ((rows i).rate : ℝ) ≤
      (Real.log 2 * mme_modern_entropyBits (beta 2).probability +
        2 * Real.log 2 + 3 * (790643 / 1000000 : ℝ) *
          ((((2 * (rows i).g + (rows i).l : ℕ) : ℝ) /
            (((rows i).l + (rows i).g : ℕ) : ℝ)) * Real.log 5)) / 3 := by
  rw [beta_entropy i beta hbeta]
  convert rate_le_publicLogRate i using 1
  simp only [logCoefficient, Rat.cast_div, Rat.cast_natCast, Rat.cast_add,
    Rat.cast_mul, Rat.cast_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- All 63 canonicalized coupled rows, with the actual public canonical
CW-square source, actual coarse-class basis, and literal first-factor Z grade. -/
theorem endpoint (K : Type u) [Field K] (i : Fin 63) :
    HasPrescribedZSixRestrictionValueAtLeast
      (CompleteSplitCanonicalSquare.obj K 5 (rho i))
      (CompleteSplitCanonicalSquare.basis K 5 (rho i) 2)
      (fun x => (CompleteSplitCanonicalSquare.label 5 (rho i) 2 x) 0)
      (profile i) (790643 / 1000000 : ℝ) (Real.exp ((rows i).rate : ℝ)) := by
  have hb := (parameterCertificate i).2.2.1
  by_cases h0 : rho i = cwSquareBlockType 1 1 2
  · obtain ⟨beta, hbeta, hv⟩ := mme_complete_split_112_prescribedZ_six_value
      (K := K) (rows i).l (rows i).g hb (profile i) rfl
      (profile_count_unrotated i h0) (790643 / 1000000)
    rw [h0]
    change HasPrescribedZSixRestrictionValueAtLeast
      (canonicalObj K 5) (canonicalBasis K 5 2)
      (fun x => (canonicalLabel 5 2 x) 0) (profile i) _ _
    refine ⟨(Real.exp_pos _).le, ?_⟩
    intro v hv0 hvlt cutoff
    exact hv.2 v hv0 (hvlt.trans_le
      (Real.exp_le_exp.mpr (rate_le_betaRate i beta hbeta))) cutoff
  · have hc := profile_count_rotated i h0
    rcases rho_cases i with h | h | h
    · exact (h0 h).elim
    · obtain ⟨beta, hbeta, hv⟩ := mme_complete_split_112_cyclic_prescribedZ_six_value
        (K := K) (rows i).l (rows i).g hb cyclicPerm (Or.inl rfl)
        (profile i) rfl hc (790643 / 1000000)
      rw [h]
      refine ⟨(Real.exp_pos _).le, ?_⟩
      intro v hv0 hvlt cutoff
      exact hv.2 v hv0 (hvlt.trans_le
        (Real.exp_le_exp.mpr (rate_le_betaRate i beta hbeta))) cutoff
    · obtain ⟨beta, hbeta, hv⟩ := mme_complete_split_112_cyclic_prescribedZ_six_value
        (K := K) (rows i).l (rows i).g hb (cyclicPerm.trans cyclicPerm) (Or.inr rfl)
        (profile i) rfl hc (790643 / 1000000)
      rw [h]
      refine ⟨(Real.exp_pos _).le, ?_⟩
      intro v hv0 hvlt cutoff
      exact hv.2 v hv0 (hvlt.trans_le
        (Real.exp_le_exp.mpr (rate_le_betaRate i beta hbeta))) cutoff

end MME.Coupled63Scalar


open MME Module MME.DWZRestrictedValue MME.Coupled63Scalar
universe u

theorem solution (K : Type u) [Field K] (i : Fin 63) :
    HasPrescribedZSixRestrictionValueAtLeast
      (CompleteSplitCanonicalSquare.obj K 5 (rho i))
      (CompleteSplitCanonicalSquare.basis K 5 (rho i) 2)
      (fun x => (CompleteSplitCanonicalSquare.label 5 (rho i) 2 x) 0)
      (profile i) (790643 / 1000000 : ℝ) (Real.exp ((rows i).rate : ℝ)) := MME.Coupled63Scalar.endpoint K i
