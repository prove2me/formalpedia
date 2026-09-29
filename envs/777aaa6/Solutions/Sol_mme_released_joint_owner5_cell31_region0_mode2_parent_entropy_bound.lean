-- Prove2me | solution 1 for mme_released_joint_owner5_cell31_region0_mode2_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T13:09:23.755688+00:00
-- url     : https://prove2.me/submissions/26d99107-b4aa-4131-9685-14a75971f063

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 327402057000000000000000000000000, 0, 0, 0, 0, 0, 20116208087250000000000000000000000, 0, 20116208087250000000000000000000000, 0, 0, 0, 40606264362659541216506199407680, 0, 20537126520577865167062987601184640, 0, 40606264362659541216506199407680, 0, 0, 0, 0, 0, 0, 0, 20116208087250000000000000000000000, 0, 20116208087250000000000000000000000, 0, 0, 0, 20537125566823228311690987601184640, 0, 756104594557747174877626024797630720, 0, 20537125566823228311690987601184640, 0, 0, 0, 20116210228750000000000000000000000, 0, 20116210228750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 40606264362659541216506199407680, 0, 20537126520577865167062987601184640, 0, 40606264362659541216506199407680, 0, 0, 0, 20116210228750000000000000000000000, 0, 20116210228750000000000000000000000, 0, 0, 0, 0, 0, 327400889000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 15, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8024321610213, 0, 0, 0, 0, 0, 3906229416361, 0, 3906229416361, 0, 0, 0, 10111588208613, 0, 3885520981027, 0, 10111588208613, 0, 0, 0, 0, 0, 0, 0, 3906229416361, 0, 3906229416361, 0, 0, 0, 3885521027468, 0, 279575559783, 0, 3885521027468, 0, 0, 0, 3906229309905, 0, 3906229309905, 0, 0, 0, 0, 0, 0, 0, 10111588208613, 0, 3885520981027, 0, 10111588208613, 0, 0, 0, 3906229309905, 0, 3906229309905, 0, 0, 0, 0, 0, 8024325177699, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8024321610212, 0, 0, 0, 0, 0, 3906229416360, 0, 3906229416360, 0, 0, 0, 10111588208611, 0, 3885520981026, 0, 10111588208611, 0, 0, 0, 0, 0, 0, 0, 3906229416360, 0, 3906229416360, 0, 0, 0, 3885521027467, 0, 279575559782, 0, 3885521027467, 0, 0, 0, 3906229309904, 0, 3906229309904, 0, 0, 0, 0, 0, 0, 0, 10111588208611, 0, 3885520981026, 0, 10111588208611, 0, 0, 0, 3906229309904, 0, 3906229309904, 0, 0, 0, 0, 0, 8024325177697, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1166103044 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 2) 256) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 256 c : ℚ) *
        (((integerProfile 0 1 2) ⟨256, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 2) ⟨256, c⟩ v : ℕ)) *
        (((integerProfile 0 1 2) ⟨256, complement (parent_total 0 256) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 2) ⟨256, complement (parent_total 0 256) c⟩ v : ℕ))) /
      (size 0 1 256 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 2) 256 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1166103044 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
