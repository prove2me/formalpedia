-- Prove2me | solution 1 for mme_released_interior_owner4_cell19_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:16:35.716601+00:00
-- url     : https://prove2.me/submissions/b15aa6cf-fe5e-4b5f-a6ea-4aeea92dd37c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 4 19 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(205142662741 / 500000000000), (398708187653 / 500000000000), (25640258407 / 62500000000), (1 / 1), (1 / 1)], ![(51115449026875000000000000000000000 / 2531273014823910273461864750713606077), (33453383453625000000000000000000000 / 843757671607970091153954916904535359), (1310520960875000000000000000000000 / 64904436277536160857996532069579643), (1 / 1), (1 / 1)], ![(9649268157 / 250000000000), (2254894126893 / 1000000000000), (17710930893097 / 1000000000000), (2254665713929 / 1000000000000), (38596703879 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-111362805689 / 125000000000), (-56594577093 / 250000000000), (-178200569293 / 200000000000), (0 / 1), (0 / 1)], ![(-97559771057 / 25000000000), (-1613856201689 / 500000000000), (-487811404843 / 125000000000), (0 / 1), (0 / 1)], ![(-3254578844041 / 1000000000000), (25409469421 / 31250000000), (2874182013547 / 1000000000000), (162600343961 / 200000000000), (-1627294198947 / 500000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-890902445511 / 1000000000000), (-226378308371 / 1000000000000), (-3480479869 / 3906250000), (0 / 1), (0 / 1)], ![(-3902390842279 / 1000000000000), (-3227712403377 / 1000000000000), (-3902491238743 / 1000000000000), (0 / 1), (0 / 1)], ![(-81364471101 / 25000000000), (813103021473 / 1000000000000), (718545503387 / 250000000000), (406500859903 / 500000000000), (-3254588397893 / 1000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 4 19).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-7676846701 / 4000000000), (-1657883715319 / 500000000000), (-1005985210751 / 125000000000), (-1652806114079 / 500000000000), (-2899543491 / 5000000000), (-3305613129301 / 1000000000000), (-8048072930351 / 1000000000000), (-3315766525861 / 1000000000000), (-1919211670657 / 1000000000000)] : List ℚ).getD
    ((seed 4 19).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-1919211675249 / 1000000000000), (-3315767430637 / 1000000000000), (-8047881686007 / 1000000000000), (-3305612228157 / 1000000000000), (-579908698199 / 1000000000000), (-33056131293 / 10000000000), (-160961458607 / 20000000000), (-165788326293 / 50000000000), (-14993841177 / 7812500000)] : List ℚ).getD
    ((seed 4 19).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 4 19 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
