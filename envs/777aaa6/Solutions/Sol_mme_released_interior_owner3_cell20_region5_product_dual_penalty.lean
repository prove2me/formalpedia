-- Prove2me | solution 1 for mme_released_interior_owner3_cell20_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:28:57.456066+00:00
-- url     : https://prove2.me/submissions/e93fb7c5-6e3e-4dee-8571-71b8856bbbed

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 3 20 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(171662185413841 / 500000000000000), (133450285206829 / 200000000000000), (343324360357383 / 1000000000000000), (1 / 1), (1 / 1)], ![(3424914723957 / 62500000000000), (794680648416501 / 1000000000000000), (397340308790209 / 500000000000000), (13699669356537 / 250000000000000), (1 / 1)], ![(8774138971797 / 200000000000000), (295916330700897 / 500000000000000), (591832681986647 / 1000000000000000), (43870630923083 / 1000000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![4, 0, 0, 4, 0], ![5, 1, 1, 5, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-267269897788171 / 250000000000000), (-101147088379651 / 250000000000000), (-1069079621649497 / 1000000000000000), (0 / 1), (0 / 1)], ![(-2904089983452877 / 1000000000000000), (-3590858517749 / 15625000000000), (-4596299678781 / 20000000000000), (-726022304969689 / 250000000000000), (0 / 1)], ![(-312650872488261 / 100000000000000), (-839250160971 / 1600000000000), (-524531315825333 / 1000000000000000), (-3126510182255209 / 1000000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-534539795576341 / 500000000000000), (-202294176759301 / 500000000000000), (-213815924329899 / 200000000000000), (0 / 1), (0 / 1)], ![(-2904089983452873 / 1000000000000000), (-45962989027187 / 200000000000000), (-229814983939049 / 1000000000000000), (-2904089219878751 / 1000000000000000), (0 / 1)], ![(-625301744976521 / 200000000000000), (-262265675303437 / 500000000000000), (-524531315825331 / 1000000000000000), (-781627545563801 / 250000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([9, 6, 6, 2, 3, 3, 2, 6, 6, 9] : List ℤ).getD
    ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-642153386494917 / 100000000000000), (-2213623622342453 / 500000000000000), (-899936491858387 / 200000000000000), (-289751238521003 / 250000000000000), (-1823152839746391 / 1000000000000000), (-1823152813278379 / 1000000000000000), (-1159004880651487 / 1000000000000000), (-4499683215645999 / 1000000000000000), (-4427248631187829 / 1000000000000000), (-6421536086135269 / 1000000000000000)] : List ℚ).getD
    ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-6421533864949161 / 1000000000000000), (-44272472446849 / 10000000000000), (-4499682459291929 / 1000000000000000), (-1159004954084009 / 1000000000000000), (-455788209936597 / 250000000000000), (-14585222506227 / 8000000000000), (-231800976130297 / 200000000000000), (-4499683215645993 / 1000000000000000), (-4427248631187823 / 1000000000000000), (-6421536086135261 / 1000000000000000)] : List ℚ).getD
    ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 20) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 3 20 5 c : ℝ) / 1000000000000) ≤
          (400 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (400 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((400 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
