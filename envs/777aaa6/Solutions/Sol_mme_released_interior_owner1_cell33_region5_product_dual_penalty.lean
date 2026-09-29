-- Prove2me | solution 1 for mme_released_interior_owner1_cell33_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:12:58.169567+00:00
-- url     : https://prove2.me/submissions/61682d02-15be-481e-919a-54e5a36d3e9f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 1 33 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(26699039972500000000000000000000000 / 8725117990586411337855736762817295631), (1032858407909500000000000000000000000 / 8725117990586411337855736762817295631), (6389231690928000000000000000000000000 / 8725117990586411337855736762817295631), (1032858836049500000000000000000000000 / 8725117990586411337855736762817295631), (26699039017500000000000000000000000 / 8725117990586411337855736762817295631)], ![(136089191379 / 500000000000), (1450284337333 / 1000000000000), (1450284955489 / 1000000000000), (272177879819 / 1000000000000), (1 / 1)], ![(394711201699 / 1000000000000), (394711344339 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 0, 0, 2, 0], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2894666830791 / 500000000000), (-2133875879351 / 1000000000000), (-12463678651 / 40000000000), (-2133875464831 / 1000000000000), (-723666712169 / 125000000000)], ![(-1301297608679 / 1000000000000), (4646995399 / 12500000000), (371760058151 / 1000000000000), (-1301299456509 / 1000000000000), (0 / 1)], ![(-92960091643 / 100000000000), (-232400138763 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-5789333661581 / 1000000000000), (-42677517587 / 20000000000), (-155795983137 / 500000000000), (-213387546483 / 100000000000), (-5789333697351 / 1000000000000)], ![(-650648804339 / 500000000000), (371759631921 / 1000000000000), (46470007269 / 125000000000), (-325324864127 / 250000000000), (0 / 1)], ![(-929600916429 / 1000000000000), (-929600555051 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 1 33).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-8020233674307 / 1000000000000), (-4364776252253 / 1000000000000), (-1345858188127 / 500000000000), (-108679103069 / 125000000000), (-434716444703 / 500000000000), (-134585837467 / 50000000000), (-4364773628549 / 1000000000000), (-8020232223327 / 1000000000000)] : List ℚ).getD
    ((seed 1 33).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-4010116837153 / 500000000000), (-1091194063063 / 250000000000), (-2691716376253 / 1000000000000), (-869432824551 / 1000000000000), (-173886577881 / 200000000000), (-2691716749339 / 1000000000000), (-1091193407137 / 250000000000), (-4010116111663 / 500000000000)] : List ℚ).getD
    ((seed 1 33).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 33) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 33 =>
        (splitWeight 1 33 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 33, ∏ i, weights i (c.val i) ≤ 1 := by
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
