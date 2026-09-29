-- Prove2me | solution 1 for mme_released_interior_owner1_cell25_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:27.891607+00:00
-- url     : https://prove2.me/submissions/4cdb9797-2a0c-432b-a28e-9fa18ad7d46c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 1 25 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(279458618681000000000000000000000000 / 17742403306593290605146132572132838909), (1400426482403000000000000000000000000 / 17742403306593290605146132572132838909), (1400428199989000000000000000000000000 / 17742403306593290605146132572132838909), (93153406006000000000000000000000000 / 5914134435531096868382044190710946303), (1 / 1)], ![(391458235207 / 1000000000000), (391458726593 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(13300229183 / 250000000000), (19862028133 / 10000000000), (6894486368983 / 500000000000), (993104085657 / 500000000000), (53200935159 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 4, 4, 6, 0], ![2, 2, 0, 0, 0], ![5, 0, -3, 0, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-4150858493741 / 1000000000000), (-507836124213 / 200000000000), (-2539179394593 / 1000000000000), (-2075426385387 / 500000000000), (0 / 1)], ![(-117234556019 / 125000000000), (-468937596441 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2933679650979 / 1000000000000), (686224681909 / 1000000000000), (655967298943 / 250000000000), (343113689761 / 500000000000), (-2933679304613 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-207542924687 / 50000000000), (-317397577633 / 125000000000), (-79349356081 / 31250000000), (-4150852770773 / 1000000000000), (0 / 1)], ![(-937876448151 / 1000000000000), (-937875192881 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1466839825489 / 500000000000), (68622468191 / 100000000000), (2623869195773 / 1000000000000), (686227379523 / 1000000000000), (-733419826153 / 250000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([7, 12, 2, 5, 5, 2, 12, 7] : List ℤ).getD
    ((seed 1 25).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-4402506307119 / 1000000000000), (-2005603561421 / 250000000000), (-426593309089 / 500000000000), (-279082968969 / 100000000000), (-69770747639 / 25000000000), (-85318664697 / 100000000000), (-2005601903789 / 250000000000), (-4402504536997 / 1000000000000)] : List ℚ).getD
    ((seed 1 25).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-2201253153559 / 500000000000), (-8022414245683 / 1000000000000), (-853186618177 / 1000000000000), (-2790829689689 / 1000000000000), (-2790829905559 / 1000000000000), (-853186646969 / 1000000000000), (-1604481523031 / 200000000000), (-1100626134249 / 250000000000)] : List ℚ).getD
    ((seed 1 25).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 25) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 25 =>
        (splitWeight 1 25 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 25, ∏ i, weights i (c.val i) ≤ 1 := by
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
