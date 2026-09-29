-- Prove2me | solution 1 for mme_released_interior_owner5_cell37_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:24:07.694347+00:00
-- url     : https://prove2.me/submissions/34c91911-33d3-414d-9baa-fbed741b693c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 5 37 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (4923233461 / 31250000000), (237880831237 / 62500000000), (3806095184631 / 1000000000000), (6301731889 / 40000000000)], ![(117274263607 / 200000000000), (1045649632453 / 1000000000000), (293185889699 / 500000000000), (1 / 1), (1 / 1)], ![(5259933162500000000000000000000000 / 66317304506440857300343038264042659), (15779804536000000000000000000000000 / 198951913519322571901029114792127977), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 3, -1, -1, 3], ![1, 0, 1, 0, 0], ![4, 4, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-73922154161 / 40000000000), (334150820611 / 250000000000), (66830188883 / 50000000000), (-46201373887 / 25000000000)], ![(-33362627597 / 62500000000), (44638350117 / 1000000000000), (-266900627371 / 500000000000), (0 / 1), (0 / 1)], ![(-2534332546331 / 1000000000000), (-2534332226397 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-231006731753 / 125000000000), (267320656489 / 200000000000), (1336603777661 / 1000000000000), (-1848054955479 / 1000000000000)], ![(-533802041551 / 1000000000000), (22319175059 / 500000000000), (-533801254741 / 1000000000000), (0 / 1), (0 / 1)], ![(-253433254633 / 100000000000), (-633583056599 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 5 37).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-4916189543349 / 1000000000000), (-1153090418551 / 1000000000000), (-173153051863 / 100000000000), (-108220655643 / 62500000000), (-230618118767 / 200000000000), (-307261708451 / 62500000000)] : List ℚ).getD
    ((seed 5 37).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-1229047385837 / 250000000000), (-23061808371 / 20000000000), (-1731530518629 / 1000000000000), (-1731530490287 / 1000000000000), (-576545296917 / 500000000000), (-983237467043 / 200000000000)] : List ℚ).getD
    ((seed 5 37).splits.idxOf (sourceShape 5 c)) 0

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
        (splitWeight 5 37 1 c : ℝ) / 1000000000000) ≤
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
