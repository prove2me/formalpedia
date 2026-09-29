-- Prove2me | solution 1 for mme_released_interior_owner0_cell20_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:27.47304+00:00
-- url     : https://prove2.me/submissions/346ca414-fa58-436f-a1af-b3b57a36c501

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 0 20 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(221671265584000000000000000000000000 / 8128666149607269013811311897299893271), (424345844458000000000000000000000000 / 8128666149607269013811311897299893271), (221647831975000000000000000000000000 / 8128666149607269013811311897299893271), (1 / 1), (1 / 1)], ![(2059640869 / 12500000000), (621374794589 / 250000000000), (2485363948729 / 1000000000000), (5148542501 / 31250000000), (1 / 1)], ![(169671571319 / 1000000000000), (2410968224221 / 1000000000000), (1205422300101 / 500000000000), (42409202599 / 250000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![3, -1, -1, 3, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-144078265003 / 40000000000), (-1476301665099 / 500000000000), (-3602062343999 / 1000000000000), (0 / 1), (0 / 1)], ![(-901598506071 / 500000000000), (910473515977 / 1000000000000), (182083821413 / 200000000000), (-1803305711077 / 1000000000000), (0 / 1)], ![(-88694532197 / 50000000000), (88002841961 / 100000000000), (439988571311 / 500000000000), (-887047768373 / 500000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1800978312537 / 500000000000), (-2952603330197 / 1000000000000), (-1801031171999 / 500000000000), (0 / 1), (0 / 1)], ![(-1803197012141 / 1000000000000), (455236757989 / 500000000000), (455209553533 / 500000000000), (-450826427769 / 250000000000), (0 / 1)], ![(-1773890643939 / 1000000000000), (880028419611 / 1000000000000), (879977142623 / 1000000000000), (-354819107349 / 200000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([7, 3, 7, 10, 2, 2, 10, 7, 3, 7] : List ℤ).getD
    ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-1117332077893 / 250000000000), (-1811033765783 / 1000000000000), (-4529214903977 / 1000000000000), (-50787739613 / 7812500000), (-232458052447 / 200000000000), (-1162293381887 / 1000000000000), (-3250367293711 / 500000000000), (-4529263025267 / 1000000000000), (-1811033798789 / 1000000000000), (-4469283725253 / 1000000000000)] : List ℚ).getD
    ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-446932831157 / 100000000000), (-905516882891 / 500000000000), (-566151862997 / 125000000000), (-6500830670463 / 1000000000000), (-581145131117 / 500000000000), (-581146690943 / 500000000000), (-6500734587421 / 1000000000000), (-2264631512633 / 500000000000), (-452758449697 / 250000000000), (-1117320931313 / 250000000000)] : List ℚ).getD
    ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

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
        (splitWeight 0 20 3 c : ℝ) / 1000000000000) ≤
          (1641 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1641 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1641 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
