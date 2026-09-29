-- Prove2me | solution 1 for mme_more_asymmetry_first_112_ambient_square_value_below
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T11:29:52.292906+00:00
-- url     : https://prove2.me/submissions/324d5b28-e73c-43e8-af75-0a67c421660b

import Theorems.Thm_mme_more_asymmetry_first_112_intact_six_sequence_rate
import Theorems.Thm_mme_six_sequence_rate_source_value_below
import Theorems.Thm_mme_kronPow_kronPow_isomorphic

open MME MME.DWZRestrictedValue MME.RecursiveYZ.CWCells
open scoped BigOperators
universe u
set_option autoImplicit false

/-- The first-slice rate gives a value bound for the actual square CW source. -/
theorem solution
    {K : Type u} [Field K] (tau v : ℝ) (hv : 0 < v)
    (hupper : v < Real.exp ((Real.log 2 *
        (mme_modern_entropyBits
          (fun word => (MoreAsymmetryFirstSlice.probability 0 2 word : ℝ)) + 2) +
      3 * tau * (2 - 2 * (MoreAsymmetryFirstSlice.split0 : ℝ)) * Real.log 5) / 3)) :
    HasSixSymmetricTauValueAtLeast ((CWObj K 5).kronPow 2) tau v := by
  obtain ⟨mu, _, hrate⟩ := mme_more_asymmetry_first_112_intact_six_sequence_rate.{u}
  apply mme_six_sequence_rate_source_value_below _ _ _ tau _ v (hrate K tau) _ hv hupper
  intro m
  let n := 2 * (1180591620717411303424 * m)
  have hfiltered : TensorObj.Restrict
      (unbroken K 5 2 n (Equiv.refl _) (fun _ => Unit.unit)
        (fun _ => ![1, 1, 2]) (fun i _ => mu m i)) (source K 5 2 n) := by
    exact ⟨fun i => (grading K 5 2 n (Equiv.refl _) (fun _ => Unit.unit)
      (fun _ => ![1, 1, 2]) (fun i _ => mu m i)).blockProj i 0, rfl⟩
  exact hfiltered.trans (by simpa only [source, Nat.reduceSub, pow_one] using
    (mme_kronPow_kronPow_isomorphic (CWObj K 5) 2 n).2)

#print axioms solution
