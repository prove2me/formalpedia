-- Prove2me | solution 1 for mme_six_sequence_rate_source_value_below
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T11:28:14.301531+00:00
-- url     : https://prove2.me/submissions/a1dadfd0-bd9b-4c6b-83d8-41f7ec978fd9

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic

open MME MME.DWZRestrictedValue Filter
open scoped BigOperators
universe u
set_option autoImplicit false

/-- Cofinal sequence witnesses transfer to every strict lower value of a fixed source. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3)
    (A : ℕ → TensorObj K 3) (length : ℕ → ℕ) (tau V v : ℝ)
    (hrate : HasSixSequenceRate TensorObj.Restrict A length tau V)
    (hsource : ∀ m, TensorObj.Restrict (A m) (T.kronPow (length m)))
    (hv : 0 < v) (hvV : v < V) :
    HasSixSymmetricTauValueAtLeast T tau v := by
  refine ⟨by positivity, ?_⟩
  intro epsilon hepsilon
  apply frequently_atTop.2
  intro cutoff
  obtain ⟨m, _, hlength, k, a, b, c, hextract, hweight⟩ :=
    hrate.2 v hv hvV cutoff
  refine ⟨length m, hlength, k, a, b, c, ?_, ?_⟩
  · exact hextract.trans ((mme_sixSymmetrization_restrict (hsource m)).trans
      (mme_sixSymmetrization_kronPow_isomorphic T (length m)).2)
  · calc
      (v ^ 6) ^ length m * (1 - epsilon) ≤ (v ^ 6) ^ length m := by
        exact mul_le_of_le_one_right (by positivity) (by linarith)
      _ = v ^ (6 * length m) := (pow_mul v 6 (length m)).symm
      _ ≤ _ := hweight

#print axioms solution
