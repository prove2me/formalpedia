-- Prove2me | solution 1 for mme_released_interior_owner2_cell37_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:59:44.040344+00:00
-- url     : https://prove2.me/submissions/e0038c14-42c0-4a8f-8edd-5fb97eef18c2

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 2 37 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (31488905307 / 200000000000), (1904338543989 / 500000000000), (761736726287 / 200000000000), (78722284849 / 500000000000)], ![(29313625958600000000000000000000000 / 377987887560761508552690265147893921), (52302672512500000000000000000000000 / 377987887560761508552690265147893921), (29313719897600000000000000000000000 / 377987887560761508552690265147893921), (1 / 1), (1 / 1)], ![(59909434323 / 100000000000), (4680431373 / 7812500000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![4, 3, 4, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-369736419047 / 200000000000), (2089502981 / 1562500000), (668641812939 / 500000000000), (-1848681821087 / 1000000000000)], ![(-1278404846957 / 500000000000), (-988907341093 / 500000000000), (-25568064893 / 10000000000), (0 / 1), (0 / 1)], ![(-512336192051 / 1000000000000), (-512334735663 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-924341047617 / 500000000000), (1337281907841 / 1000000000000), (1337283625879 / 1000000000000), (-924340910543 / 500000000000)], ![(-2556809693913 / 1000000000000), (-395562936437 / 200000000000), (-2556806489299 / 1000000000000), (0 / 1), (0 / 1)], ![(-10246723841 / 20000000000), (-256167367831 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([3, 8, 2, 2, 8, 3] : List ℤ).getD
    ((seed 2 37).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-865930401851 / 500000000000), (-2458913853561 / 500000000000), (-115286751001 / 100000000000), (-1152867248353 / 1000000000000), (-4917823320257 / 1000000000000), (-432965193377 / 250000000000)] : List ℚ).getD
    ((seed 2 37).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-1731860803701 / 1000000000000), (-4917827707121 / 1000000000000), (-1152867510009 / 1000000000000), (-36027101511 / 31250000000), (-76840989379 / 15625000000), (-1731860773507 / 1000000000000)] : List ℚ).getD
    ((seed 2 37).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 37 3 c : ℝ) / 1000000000000) ≤
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
