-- Prove2me | solution 1 for mme_released_interior_owner2_cell14_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:19:52.954276+00:00
-- url     : https://prove2.me/submissions/9a124a90-6bcc-4a92-9fc0-23b76d49f3dd

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 2 14 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(37322900281 / 62500000000), (119433354689 / 200000000000), (1 / 1), (1 / 1), (1 / 1)], ![(1 / 1), (155200705111000000000000000000000000 / 7622875785811943255526083140861716459), (3847444305898000000000000000000000000 / 7622875785811943255526083140861716459), (3847446916676000000000000000000000000 / 7622875785811943255526083140861716459), (155200589672000000000000000000000000 / 7622875785811943255526083140861716459)], ![(145439177439 / 250000000000), (1053678131919 / 1000000000000), (581757434751 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 1, 0, 0, 0], ![0, 6, 1, 1, 6], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-51555946993 / 100000000000), (-515558852097 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-3894189826217 / 1000000000000), (-683744586989 / 1000000000000), (-341871954207 / 500000000000), (-1947095285011 / 500000000000)], ![(-270851471561 / 500000000000), (10457405159 / 200000000000), (-270850848453 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-515559469929 / 1000000000000), (-1006950883 / 1953125000), (0 / 1), (0 / 1), (0 / 1)], ![(0 / 1), (-486773728277 / 125000000000), (-170936146747 / 250000000000), (-683743908413 / 1000000000000), (-3894190570021 / 1000000000000)], ![(-541702943121 / 1000000000000), (13071756449 / 250000000000), (-108340339381 / 200000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 14) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-2475725187607 / 500000000000), (-69640230153 / 40000000000), (-1147016413289 / 1000000000000), (-573508176273 / 500000000000), (-1741005703633 / 1000000000000), (-4951452983111 / 1000000000000)] : List ℚ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 14) : ℚ :=
  ([(-4951450375213 / 1000000000000), (-54406429807 / 31250000000), (-143377051661 / 125000000000), (-229403270509 / 200000000000), (-108812856477 / 62500000000), (-495145298311 / 100000000000)] : List ℚ).getD
    ((seed 2 14).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 14) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 14 =>
        (splitWeight 2 14 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 14, ∏ i, weights i (c.val i) ≤ 1 := by
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
