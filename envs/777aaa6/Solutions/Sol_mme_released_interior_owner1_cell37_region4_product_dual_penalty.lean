-- Prove2me | solution 1 for mme_released_interior_owner1_cell37_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:13:00.751904+00:00
-- url     : https://prove2.me/submissions/050a12d0-80c2-4ea9-bfa7-f44dc750e067

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 1 37 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (31418203704800000000000000000000000 / 1515538640440265412279924122362606583), (108932633541400000000000000000000000 / 216505520062895058897132017480372369), (762527837865200000000000000000000000 / 1515538640440265412279924122362606583), (31418165754800000000000000000000000 / 1515538640440265412279924122362606583)], ![(116854688551 / 200000000000), (210178296121 / 200000000000), (584272532403 / 1000000000000), (1 / 1), (1 / 1)], ![(299462618993 / 500000000000), (598924762659 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1938069366123 / 500000000000), (-343443196843 / 500000000000), (-686887176509 / 1000000000000), (-775227988029 / 200000000000)], ![(-537386181841 / 1000000000000), (9927766619 / 200000000000), (-107477547987 / 200000000000), (0 / 1), (0 / 1)], ![(-8009664063 / 15625000000), (-256309646833 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-775227746449 / 200000000000), (-137377278737 / 200000000000), (-171721794127 / 250000000000), (-242258746259 / 62500000000)], ![(-6717327273 / 12500000000), (6204854137 / 125000000000), (-268693869967 / 500000000000), (0 / 1), (0 / 1)], ![(-512618500031 / 1000000000000), (-102523858733 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 37) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-4926145765909 / 1000000000000), (-1736892633653 / 1000000000000), (-1149866854257 / 1000000000000), (-1149866843441 / 1000000000000), (-347378530403 / 200000000000), (-2463072311027 / 500000000000)] : List ℚ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 37) : ℚ :=
  ([(-1231536441477 / 250000000000), (-434223158413 / 250000000000), (-71866678391 / 62500000000), (-14373335543 / 12500000000), (-868446326007 / 500000000000), (-4926144622053 / 1000000000000)] : List ℚ).getD
    ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 37 4 c : ℝ) / 1000000000000) ≤
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
