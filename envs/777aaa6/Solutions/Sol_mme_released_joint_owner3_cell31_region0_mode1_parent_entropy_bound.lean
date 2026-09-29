-- Prove2me | solution 1 for mme_released_joint_owner3_cell31_region0_mode1_parent_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T10:04:04.779978+00:00
-- url     : https://prove2.me/submissions/ca994ef1-ce76-49bf-ae6e-cc83a4e98817

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
  ([0, 0, 0, 0, 0, 0, 0, 0, 324717744000000000000000000000000, 0, 0, 0, 0, 0, 19434439737500000000000000000000000, 0, 19434439737500000000000000000000000, 0, 0, 0, 69962663577301923275890247478660, 0, 20728922618022396591281219505042680, 0, 69962663577301923275890247478660, 0, 0, 0, 0, 0, 0, 0, 19434439737500000000000000000000000, 0, 19434439737500000000000000000000000, 0, 0, 0, 20728922221033610664828219505042680, 0, 760679501804578777794677560989914640, 0, 20728922221033610664828219505042680, 0, 0, 0, 19434440237750000000000000000000000, 0, 19434440237750000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 69962663577301923275890247478660, 0, 20728922618022396591281219505042680, 0, 69962663577301923275890247478660, 0, 0, 0, 19434440237750000000000000000000000, 0, 19434440237750000000000000000000000, 0, 0, 0, 0, 0, 324720218000000000000000000000000, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def logScale (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 14, 0, 6, 0, 14, 0, 0, 0, 0, 0, 0, 0, 6, 0, 6, 0, 0, 0, 6, 0, 1, 0, 6, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 0, 0, 14, 0, 6, 0, 14, 0, 0, 0, 6, 0, 6, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def lowerMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8032554232982, 0, 0, 0, 0, 0, 3940708542596, 0, 3940708542596, 0, 0, 0, 9567548835679, 0, 3876225326002, 0, 9567548835679, 0, 0, 0, 0, 0, 0, 0, 3940708542596, 0, 3940708542596, 0, 0, 0, 3876225345154, 0, 273543163833, 0, 3876225345154, 0, 0, 0, 3940708516856, 0, 3940708516856, 0, 0, 0, 0, 0, 0, 0, 9567548835679, 0, 3876225326002, 0, 9567548835679, 0, 0, 0, 3940708516856, 0, 3940708516856, 0, 0, 0, 0, 0, 8032546614087, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

private def upperMagnitude (w : Fin 2 → CompleteWord 2) : ℕ :=
  ([0, 0, 0, 0, 0, 0, 0, 0, 8032554232981, 0, 0, 0, 0, 0, 3940708542595, 0, 3940708542595, 0, 0, 0, 9567548835678, 0, 3876225326001, 0, 9567548835678, 0, 0, 0, 0, 0, 0, 0, 3940708542595, 0, 3940708542595, 0, 0, 0, 3876225345153, 0, 273543163832, 0, 3876225345153, 0, 0, 0, 3940708516855, 0, 3940708516855, 0, 0, 0, 0, 0, 0, 0, 9567548835678, 0, 3876225326001, 0, 9567548835678, 0, 0, 0, 3940708516855, 0, 3940708516855, 0, 0, 0, 0, 0, 8032546614086, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ).getD (wordIndex w) 0

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
    (1150056410 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 1) 166) := by
  have hid : ∀ w, p w = (∑ c, (splitCount 0 1 166 c : ℚ) *
        (((integerProfile 0 1 1) ⟨166, c⟩ (w 0) : ℚ) / (∑ v, (integerProfile 0 1 1) ⟨166, c⟩ v : ℕ)) *
        (((integerProfile 0 1 1) ⟨166, complement (parent_total 0 166) c⟩ (w 1) : ℚ) /
          (∑ v, (integerProfile 0 1 1) ⟨166, complement (parent_total 0 166) c⟩ v : ℕ))) /
      (size 0 1 166 : ℚ) := by
    decide +kernel
  have he : (fun w => (p w : ℝ)) =
      RegionRealization.parentMixture (parent_total 0) (size 0 1)
        (splitCount 0 1) (integerProfile 0 1 1) 166 := by
    funext w
    rw [mme_parent_mixture_rational_identity]
    exact_mod_cast hid w
  have hc : (1150056410 / 1000000000 : ℚ) ≤ -(∑ w, p w * upper w) := by
    decide +kernel
  have h := ((Rat.cast_le (K := ℝ)).2 hc).trans
    (mme_rational_entropy_log_bounds p p_nonneg lower upper log_bounds).1
  rw [he] at h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] at h
  convert h using 1
  norm_num


#print axioms solution
