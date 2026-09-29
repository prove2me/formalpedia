-- Prove2me | solution 1 for mme_released_interior_owner5_cell20_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:20:59.296682+00:00
-- url     : https://prove2.me/submissions/10cfdccc-5206-46a8-93fe-8afe26de3138

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 5 20 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(444424014797 / 1000000000000), (431871923883 / 500000000000), (444466206581 / 1000000000000), (1 / 1), (1 / 1)], ![(175597667997 / 1000000000000), (1176493006971 / 500000000000), (1176548550997 / 500000000000), (43905984997 / 250000000000), (1 / 1)], ![(33681490770800000000000000000000000 / 3183274104487375999216944753067556567), (491486238997600000000000000000000000 / 3183274104487375999216944753067556567), (491509671658600000000000000000000000 / 3183274104487375999216944753067556567), (33686029881000000000000000000000000 / 3183274104487375999216944753067556567), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![3, -1, -1, 3, 0], ![7, 3, 3, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-40548809199 / 50000000000), (-36619756657 / 250000000000), (-3167504893 / 3906250000), (0 / 1), (0 / 1)], ![(-1739559878069 / 1000000000000), (855685165801 / 1000000000000), (855732376209 / 1000000000000), (-217426284321 / 125000000000), (0 / 1)], ![(-568589635941 / 125000000000), (-1868231597489 / 1000000000000), (-46704598037 / 25000000000), (-4548582330893 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-810976183979 / 1000000000000), (-146479026627 / 1000000000000), (-810881252607 / 1000000000000), (0 / 1), (0 / 1)], ![(-434889969517 / 250000000000), (427842582901 / 500000000000), (85573237621 / 100000000000), (-1739410274567 / 1000000000000), (0 / 1)], ![(-4548717087527 / 1000000000000), (-116764474843 / 62500000000), (-1868183921479 / 1000000000000), (-1137145582723 / 250000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 5 20).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-180235086403 / 40000000000), (-3210424486311 / 500000000000), (-364630466893 / 200000000000), (-1159049101141 / 1000000000000), (-4420464754633 / 1000000000000), (-2210235866501 / 500000000000), (-231809727337 / 200000000000), (-911576189701 / 500000000000), (-6420863842999 / 1000000000000), (-4505884526613 / 1000000000000)] : List ℚ).getD
    ((seed 5 20).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-2252938580037 / 500000000000), (-6420848972621 / 1000000000000), (-14243377613 / 7812500000), (-57952455057 / 50000000000), (-552558094329 / 125000000000), (-4420471733001 / 1000000000000), (-289762159171 / 250000000000), (-1823152379401 / 1000000000000), (-3210431921499 / 500000000000), (-1126471131653 / 250000000000)] : List ℚ).getD
    ((seed 5 20).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 20) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 5 20 1 c : ℝ) / 1000000000000) ≤
          (407 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (407 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((407 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
