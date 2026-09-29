-- Prove2me | solution 1 for mme_dwz_prescribed_z_restriction_value_forget_profile_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T06:15:37.526417+00:00
-- url     : https://prove2.me/submissions/bfc053d6-d0cc-431b-86e1-2b706b58c0af

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic

set_option autoImplicit false
set_option warningAsError true

universe u

open MME MME.DWZRestrictedValue MME.DWZComponentRestriction Module BigOperators Filter

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (tau V W : ℝ)
    (hW : 0 ≤ W) (hWV : W < V)
    (h : HasPrescribedZSixRestrictionValueAtLeast T bZ grade p tau V) :
    HasSixSymmetricTauValueAtLeast T tau W := by
  classical
  obtain ⟨v, hWv, hvV⟩ := exists_between hWV
  have hv : 0 < v := lt_of_le_of_lt hW hWv
  refine ⟨pow_nonneg hW 6, ?_⟩
  intro epsilon hepsilon
  apply Filter.frequently_atTop.2
  intro cutoff
  obtain ⟨m, _hm, hlength, k, a, b, c, hR, hweight⟩ := h.2 v hv hvV cutoff
  refine ⟨p.length m, hlength, k, a, b, c, ?_, ?_⟩
  · have hp : TensorObj.Restrict (prescribedZPower T bZ grade p m)
        (T.kronPow (p.length m)) :=
      (mme_basisZAllowedSubtensor_projection_certificate _
        (kronPowModeBasis T 2 bZ (p.length m)) (prescribedZWord grade p m)).1
    exact hR.trans ((mme_sixSymmetrization_restrict hp).trans
      (mme_sixSymmetrization_kronPow_isomorphic T (p.length m)).2)
  · have hpow : W ^ (6 * p.length m) ≤ v ^ (6 * p.length m) :=
      pow_le_pow_left₀ hW hWv.le _
    calc
      (W ^ 6) ^ p.length m * (1 - epsilon) ≤ (W ^ 6) ^ p.length m :=
        mul_le_of_le_one_right (pow_nonneg (pow_nonneg hW _) _) (by linarith)
      _ = W ^ (6 * p.length m) := (pow_mul W 6 (p.length m)).symm
      _ ≤ v ^ (6 * p.length m) := hpow
      _ ≤ ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := hweight
