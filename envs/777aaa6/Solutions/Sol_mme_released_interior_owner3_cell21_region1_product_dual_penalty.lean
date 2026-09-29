-- Prove2me | solution 1 for mme_released_interior_owner3_cell21_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:12:21.012503+00:00
-- url     : https://prove2.me/submissions/45ad766a-aa51-45eb-9eab-cf7a17dc075a

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 3 21 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(209213403387 / 500000000000), (48527282371 / 62500000000), (83685172679 / 200000000000), (1 / 1), (1 / 1)], ![(389665719 / 10000000000), (1146124343617 / 500000000000), (17113118660831 / 1000000000000), (1146121704539 / 500000000000), (7793314211 / 200000000000)], ![(402748117023000000000000000000000000 / 19977072187865470032248107985049959843), (839334386671000000000000000000000000 / 19977072187865470032248107985049959843), (402747245102000000000000000000000000 / 19977072187865470032248107985049959843), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![5, -1, -4, -1, 5], ![6, 5, 6, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-871253298557 / 1000000000000), (-253040393843 / 1000000000000), (-174251110629 / 200000000000), (0 / 1), (0 / 1)], ![(-3245051131169 / 1000000000000), (3318133181 / 4000000000), (2839845342529 / 1000000000000), (207382748159 / 250000000000), (-1622525576427 / 500000000000)], ![(-156161166303 / 40000000000), (-3169731323417 / 1000000000000), (-1952015661253 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-217813324639 / 250000000000), (-126520196921 / 500000000000), (-108906944143 / 125000000000), (0 / 1), (0 / 1)], ![(-101407847849 / 31250000000), (829533295251 / 1000000000000), (283984534253 / 100000000000), (829530992637 / 1000000000000), (-3245051152853 / 1000000000000)], ![(-1952014578787 / 500000000000), (-396216415427 / 125000000000), (-780806264501 / 200000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-1604066721673 / 200000000000), (-3327538601549 / 1000000000000), (-387087871513 / 200000000000), (-3211453591269 / 1000000000000), (-72865796841 / 125000000000), (-642290723877 / 200000000000), (-48385982229 / 25000000000), (-3327538378341 / 1000000000000), (-1002542250923 / 125000000000)] : List ℚ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-2005083402091 / 250000000000), (-831884650387 / 250000000000), (-483859839391 / 250000000000), (-802863397817 / 250000000000), (-582926374727 / 1000000000000), (-401431702423 / 125000000000), (-1935439289159 / 1000000000000), (-166376918917 / 50000000000), (-8020338007383 / 1000000000000)] : List ℚ).getD
    ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 21) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 3 21 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 21, ∏ i, weights i (c.val i) ≤ 1 := by
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
