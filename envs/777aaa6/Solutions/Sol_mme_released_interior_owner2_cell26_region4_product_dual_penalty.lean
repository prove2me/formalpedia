-- Prove2me | solution 1 for mme_released_interior_owner2_cell26_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:40:36.789115+00:00
-- url     : https://prove2.me/submissions/05397182-88a3-4c3d-9d49-ff9b9b8360e7

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 2 26 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(176486615693 / 1000000000000), (2344355297237 / 1000000000000), (293011310127 / 125000000000), (44107251723 / 250000000000), (1 / 1)], ![(11121988359500000000000000000000000 / 397051605290701097901757209575805071), (21611703526250000000000000000000000 / 397051605290701097901757209575805071), (11119485130250000000000000000000000 / 397051605290701097901757209575805071), (1 / 1), (1 / 1)], ![(84260128119 / 500000000000), (307362169809 / 125000000000), (1229310855369 / 500000000000), (21057601529 / 125000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![6, 5, 6, 0, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-433627559313 / 250000000000), (852010437547 / 1000000000000), (170379494417 / 200000000000), (-346967342153 / 200000000000), (0 / 1)], ![(-446892772279 / 125000000000), (-582166252501 / 200000000000), (-446920909233 / 125000000000), (0 / 1), (0 / 1)], ![(-1780699321353 / 1000000000000), (224928255299 / 250000000000), (44980045637 / 50000000000), (-356210424919 / 200000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1734510237251 / 1000000000000), (213002609387 / 250000000000), (425948736043 / 500000000000), (-433709177691 / 250000000000), (0 / 1)], ![(-3575142178231 / 1000000000000), (-363853907813 / 125000000000), (-3575367273863 / 1000000000000), (0 / 1), (0 / 1)], ![(-222587415169 / 125000000000), (899713021197 / 1000000000000), (899600912741 / 1000000000000), (-890526062297 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([7, 3, 7, 10, 2, 2, 10, 7, 3, 7] : List ℤ).getD
    ((seed 2 26).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-1126563860813 / 250000000000), (-1823360208811 / 1000000000000), (-2206075812513 / 500000000000), (-1603086501969 / 250000000000), (-1159292888361 / 1000000000000), (-1159293743259 / 1000000000000), (-6412319630697 / 1000000000000), (-882432463947 / 200000000000), (-911680115261 / 500000000000), (-112656018303 / 25000000000)] : List ℚ).getD
    ((seed 2 26).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-4506255443251 / 1000000000000), (-182336020881 / 100000000000), (-176486065001 / 40000000000), (-51298768063 / 8000000000), (-28982322209 / 25000000000), (-579646871629 / 500000000000), (-801539953837 / 125000000000), (-2206081159867 / 500000000000), (-1823360230521 / 1000000000000), (-4506240732119 / 1000000000000)] : List ℚ).getD
    ((seed 2 26).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 26) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 26 =>
        (splitWeight 2 26 4 c : ℝ) / 1000000000000) ≤
          (428 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (428 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((428 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
