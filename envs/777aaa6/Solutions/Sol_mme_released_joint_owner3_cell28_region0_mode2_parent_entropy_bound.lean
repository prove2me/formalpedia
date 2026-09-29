-- Prove2me | solution 1 for mme_released_joint_owner3_cell28_region0_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T12:52:56.27519+00:00
-- url     : https://prove2.me/submissions/881e1981-ba16-4b9a-b69e-77c23ec55fba

import Theorems.Thm_mme_parent_mixture_rational_identity
import Theorems.Thm_mme_rational_entropy_log_bounds
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_joint_interior_profiles

open scoped BigOperators
open MME MME.RegionRate MME.ReleasedJointInterior MME.RecursiveYZ
open MME.MoreAsymmetryExactSeed MME.CompleteSplit

private def wordIndex (w : Fin 2 → CompleteWord 2) : ℕ :=
  27 * (w 0 0).val + 9 * (w 0 1).val + 3 * (w 1 0).val + (w 1 1).val

private def pNumerator (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 330509153000000000000000000000000, 0, 0, 0, 0, 0, 19439075191250000000000000000000000, 0, 19439075191250000000000000000000000, 0, 0, 0, 24917495346699802725879473560770, 0, 20308137854937497701426241052878460, 0, 24917495346699802725879473560770, 0, 0, 0, 0, 0, 0, 0, 19439075191250000000000000000000000, 0, 19439075191250000000000000000000000, 0, 0, 0, 20308139175871425132334241052878460, 0, 762494164650995355121575517894243080, 0, 20308139175871425132334241052878460, 0, 0, 0, 19439073216250000000000000000000000, 0, 19439073216250000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 24917495346699802725879473560770, 0, 20308137854937497701426241052878460, 0, 24917495346699802725879473560770, 0, 0, 0, 19439073216250000000000000000000000, 0, 19439073216250000000000000000000000, 0, 0, 0, 0, 0, 330508523000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 16, 0, 6, 0, 16, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8014876204654, 0, 0, 0, 0, 0, 3940470053549, 0, 3940470053549, 0, 0, 0, 10599940376854, 0, 3896733593712, 0, 10599940376854, 0, 0, 0, 0, 0, 0, 0, 3940470053549, 0, 3940470053549, 0, 0, 0, 3896733528668, 0, 271160423447, 0, 3896733528668, 0, 0, 0, 3940470155148, 0, 3940470155148, 0, 0, 0, 0, 0, 0, 0, 10599940376854, 0, 3896733593712, 0, 10599940376854, 0, 0, 0, 3940470155148, 0, 3940470155148, 0, 0, 0, 0, 0, 8014878110806, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8014876204653, 0, 0, 0, 0, 0, 3940470053548, 0, 3940470053548, 0, 0, 0, 10599940376853, 0, 3896733593711, 0, 10599940376853, 0, 0, 0, 0, 0, 0, 0, 3940470053548, 0, 3940470053548, 0, 0, 0, 3896733528667, 0, 271160423446, 0, 3896733528667, 0, 0, 0, 3940470155147, 0, 3940470155147, 0, 0, 0, 0, 0, 0, 0, 10599940376853, 0, 3896733593711, 0, 10599940376853, 0, 0, 0, 3940470155147, 0, 3940470155147, 0, 0, 0, 0, 0, 8014878110805, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def p (w : Fin 2 → CompleteWord 2) : ℚ :=
  (pNumerator w : ℚ) / 1000000000000000000000000000000000000

private def lower (w : Fin 2 → CompleteWord 2) : ℚ :=
  -(lowerMagnitude w : ℚ) / 1000000000000

private def upper (w : Fin 2 → CompleteWord 2) : ℚ :=
  -(upperMagnitude w : ℚ) / 1000000000000

private theorem p_nonneg : ∀ w, 0 ≤ p w := by decide +kernel

private theorem log_bounds (w : Fin 2 → CompleteWord 2) (hp : 0 < p w) :
    (lower w : ℝ) ≤ Real.log (p w : ℝ) ∧
      Real.log (p w : ℝ) ≤ (upper w : ℝ) := by
  apply mme_rational_log_series_certificate (p w) hp (logScale w) 16
  all_goals revert w; decide +kernel

/-- A certified entropy lower bound for an actual pooled parent distribution,
including its owner, parent grade, regional orientation, and retained mode. -/
theorem solution :
    (1142447057 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 2) 163) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 163 c : ℚ) *
        (((integerProfile 0 1 2) ⟨163, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 2) ⟨163, c⟩ v : ℕ)) *
        (((integerProfile 0 1 2) ⟨163, complement (parent_total 0 163) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 2) ⟨163, complement (parent_total 0 163) c⟩ v : ℕ))) /
      (size 0 1 163 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 2) 163 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1142447057 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  exact h


#print axioms solution
