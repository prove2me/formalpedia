-- Prove2me | solution 1 for mme_released_interior_owner0_cell37_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:15.691093+00:00
-- url     : https://prove2.me/submissions/2b583bb2-5c0f-4fa2-850f-528a2e265faf

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 0 37 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (157105988323000000000000000000000000 / 7577407206265561426433267756214883621), (3812353865315000000000000000000000000 / 7577407206265561426433267756214883621), (3812356192167000000000000000000000000 / 7577407206265561426433267756214883621), (157106069865000000000000000000000000 / 7577407206265561426433267756214883621)], ![(292135945973 / 500000000000), (105091967753 / 100000000000), (116854521707 / 200000000000), (1 / 1), (1 / 1)], ![(299467847687 / 500000000000), (598936069783 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-193800285023 / 50000000000), (-686924273129 / 1000000000000), (-10733182231 / 15625000000), (-775201036287 / 200000000000)], ![(-537388836097 / 1000000000000), (49665664169 / 1000000000000), (-537387609633 / 1000000000000), (0 / 1), (0 / 1)], ![(-512601039929 / 1000000000000), (-102520082961 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-3876005700459 / 1000000000000), (-85865534141 / 125000000000), (-686923662783 / 1000000000000), (-1938002590717 / 500000000000)], ![(-2099175141 / 3906250000), (4966566417 / 100000000000), (-16793362801 / 31250000000), (0 / 1), (0 / 1)], ![(-64075129991 / 125000000000), (-128150103701 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-4925993724847 / 1000000000000), (-574929511883 / 500000000000), (-434228230673 / 250000000000), (-434228228421 / 250000000000), (-1149859038541 / 1000000000000), (-492599505749 / 100000000000)] : List ℚ).getD
    ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-2462996862423 / 500000000000), (-229971804753 / 200000000000), (-1736912922691 / 1000000000000), (-1736912913683 / 1000000000000), (-57492951927 / 50000000000), (-4925995057489 / 1000000000000)] : List ℚ).getD
    ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 37) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 37 =>
        (splitWeight 0 37 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 37, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
