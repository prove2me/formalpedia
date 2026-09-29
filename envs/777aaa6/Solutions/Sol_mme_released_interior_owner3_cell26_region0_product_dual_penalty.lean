-- Prove2me | solution 1 for mme_released_interior_owner3_cell26_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:12:38.128459+00:00
-- url     : https://prove2.me/submissions/c73f7412-e8cf-40d4-9ed2-fc0d921ab3e7

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 3 26 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(171230784669 / 1000000000000), (2392725795281 / 1000000000000), (2392821487649 / 1000000000000), (171252443149 / 1000000000000), (1 / 1)], ![(55453555239 / 125000000000), (849825631631 / 1000000000000), (221832053521 / 500000000000), (1 / 1), (1 / 1)], ![(2349192404600000000000000000000000 / 231524599348493343311963606889526187), (249284275688500000000000000000000000 / 1620672195439453403183745248226683309), (249294341122200000000000000000000000 / 1620672195439453403183745248226683309), (16446228292700000000000000000000000 / 1620672195439453403183745248226683309), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![2, 1, 2, 0, 0], ![7, 3, 3, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-110296438403 / 62500000000), (109054152023 / 125000000000), (43623660421 / 50000000000), (-1764616535379 / 1000000000000), (0 / 1)], ![(-812767909439 / 1000000000000), (-813620449 / 5000000000), (-203171879631 / 250000000000), (0 / 1), (0 / 1)], ![(-4590614517091 / 1000000000000), (-936001181467 / 500000000000), (-935980993209 / 500000000000), (-2295250054909 / 500000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1764743014447 / 1000000000000), (174486643237 / 200000000000), (872473208421 / 1000000000000), (-882308267689 / 500000000000), (0 / 1)], ![(-406383954719 / 500000000000), (-162724089799 / 1000000000000), (-812687518523 / 1000000000000), (0 / 1), (0 / 1)], ![(-459061451709 / 100000000000), (-1872002362933 / 1000000000000), (-1871961986417 / 1000000000000), (-4590500109817 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 26) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-2267378256499 / 500000000000), (-6489761858941 / 1000000000000), (-1811739608261 / 1000000000000), (-290597062697 / 250000000000), (-4453006737427 / 1000000000000), (-278313276723 / 62500000000), (-581193934017 / 500000000000), (-1811739630413 / 1000000000000), (-6489773919631 / 1000000000000), (-4534762466591 / 1000000000000)] : List ℚ).getD
    ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 26) : ℚ :=
  ([(-4534756512997 / 1000000000000), (-324488092947 / 50000000000), (-90586980413 / 50000000000), (-1162388250787 / 1000000000000), (-2226503368713 / 500000000000), (-4453012427567 / 1000000000000), (-1162387868033 / 1000000000000), (-452934907603 / 250000000000), (-648977391963 / 100000000000), (-453476246659 / 100000000000)] : List ℚ).getD
    ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 26 0 c : ℝ) / 1000000000000) ≤
          (1564 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 26, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1564 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1564 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
