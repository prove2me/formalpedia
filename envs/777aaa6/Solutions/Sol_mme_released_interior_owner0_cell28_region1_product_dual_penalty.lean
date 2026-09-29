-- Prove2me | solution 1 for mme_released_interior_owner0_cell28_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:00.117143+00:00
-- url     : https://prove2.me/submissions/29eb96d4-a249-4cf1-ab5c-5f1ef6a9f3f9

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 0 28 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(275044785272000000000000000000000000 / 17564056450316861961618323464478101721), (1430372456419000000000000000000000000 / 17564056450316861961618323464478101721), (1430366127109000000000000000000000000 / 17564056450316861961618323464478101721), (275040961505000000000000000000000000 / 17564056450316861961618323464478101721), (1 / 1)], ![(26659403391 / 500000000000), (2034647598267 / 1000000000000), (13169313321089 / 1000000000000), (2034629275211 / 1000000000000), (53318795609 / 1000000000000)], ![(78686742029 / 200000000000), (49178996077 / 125000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 4, 4, 6, 0], ![5, -1, -3, -1, 5], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2078337952857 / 500000000000), (-2507919697281 / 1000000000000), (-2507924122229 / 1000000000000), (-2078344904077 / 500000000000), (0 / 1)], ![(-586293232471 / 200000000000), (355161316757 / 500000000000), (2577889374767 / 1000000000000), (142062725591 / 200000000000), (-586293274381 / 200000000000)], ![(-116605335933 / 125000000000), (-23321177849 / 25000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-4156675905713 / 1000000000000), (-3918624527 / 1562500000), (-626981030557 / 250000000000), (-4156689808153 / 1000000000000), (0 / 1)], ![(-1465733081177 / 500000000000), (142064526703 / 200000000000), (161118085923 / 62500000000), (177578406989 / 250000000000), (-45804162061 / 15625000000)], ![(-932842687463 / 1000000000000), (-932847113959 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 28) : ℤ :=
  ([7, 12, 2, 4, 4, 2, 12, 7] : List ℤ).getD
    ((seed 0 28).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-4379209391713 / 1000000000000), (-8020984965157 / 1000000000000), (-431438718237 / 500000000000), (-341306094599 / 125000000000), (-2730448602673 / 1000000000000), (-215719358731 / 250000000000), (-4010501542123 / 500000000000), (-2189604931073 / 500000000000)] : List ℚ).getD
    ((seed 0 28).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 28) : ℚ :=
  ([(-136850293491 / 31250000000), (-2005246241289 / 250000000000), (-862877436473 / 1000000000000), (-2730448756791 / 1000000000000), (-170653037667 / 62500000000), (-862877434923 / 1000000000000), (-1604200616849 / 200000000000), (-875841972429 / 200000000000)] : List ℚ).getD
    ((seed 0 28).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 28) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 28 =>
        (splitWeight 0 28 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 28, ∏ i, weights i (c.val i) ≤ 1 := by
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
