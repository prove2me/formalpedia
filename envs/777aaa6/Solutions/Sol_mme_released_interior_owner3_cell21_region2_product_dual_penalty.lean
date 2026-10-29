-- Prove2me | solution 1 for mme_released_interior_owner3_cell21_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:12:17.298989+00:00
-- url     : https://prove2.me/submissions/0ba0895d-87e4-449a-908b-374b002e8d74

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 3 21 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(763511638970092364883610299 / 2000000000000000000000000000), (18824113836857511758861631423 / 25000000000000000000000000000), (38175580376899318244196231003 / 100000000000000000000000000000), (1 / 1), (1 / 1)], ![(136411181392298635888186077 / 50000000000000000000000000000), (16183633527508138163664724917 / 100000000000000000000000000000), (14779339467535752206605324641 / 12500000000000000000000000000), (3236726544671667632734553283 / 20000000000000000000000000000), (272821977757697271780222423 / 100000000000000000000000000000)], ![(6402683005972835973169940271 / 20000000000000000000000000000), (12473802509348575261974906513 / 20000000000000000000000000000), (400167706083695998322939163 / 1250000000000000000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![9, 3, 0, 3, 9], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-19259481815379 / 20000000000000), (-70934281507389 / 250000000000000), (-481487065968383 / 500000000000000), (0 / 1), (0 / 1)], ![(-5904104567343841 / 1000000000000000), (-910584865251177 / 500000000000000), (20937697406003 / 125000000000000), (-1821169780191431 / 1000000000000000), (-2952052989309039 / 500000000000000)], ![(-1139015151353131 / 1000000000000000), (-236050813879223 / 500000000000000), (-45560604233849 / 40000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-240743522692237 / 250000000000000), (-56747425205911 / 200000000000000), (-240743532984191 / 250000000000000), (0 / 1), (0 / 1)], ![(-5904104567343833 / 1000000000000000), (-36423394610047 / 20000000000000), (6700063169921 / 40000000000000), (-455292445047857 / 250000000000000), (-5904105978618069 / 1000000000000000)], ![(-142376893919141 / 125000000000000), (-118025406939611 / 250000000000000), (-569507552923111 / 500000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8006095220740039 / 1000000000000000), (-1621961029084067 / 500000000000000), (-967243851940733 / 500000000000000), (-814061374529347 / 250000000000000), (-147084293634987 / 250000000000000), (-814061372699737 / 250000000000000), (-967243808763749 / 500000000000000), (-3243921961784061 / 1000000000000000), (-8006093805126631 / 1000000000000000)] : List ℚ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-2001523805185007 / 250000000000000), (-3243922058168129 / 1000000000000000), (-1934487703881463 / 1000000000000000), (-3256245498117383 / 1000000000000000), (-294168587269973 / 500000000000000), (-3256245490798943 / 1000000000000000), (-386897523505499 / 200000000000000), (-405490245223007 / 125000000000000), (-8006093805126621 / 1000000000000000)] : List ℚ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 3 21 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
