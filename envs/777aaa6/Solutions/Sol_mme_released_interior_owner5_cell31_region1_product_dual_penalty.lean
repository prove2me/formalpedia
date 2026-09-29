-- Prove2me | solution 1 for mme_released_interior_owner5_cell31_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:22:51.600832+00:00
-- url     : https://prove2.me/submissions/c5a3b443-5189-47ba-9011-7541dc5fc30c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 5 31 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(53326423911 / 1000000000000), (1017000958313 / 500000000000), (6566335510089 / 500000000000), (127125337643 / 62500000000), (833225343 / 15625000000)], ![(19644976019 / 50000000000), (98224971937 / 250000000000), (1 / 1), (1 / 1), (1 / 1)], ![(68229710216750000000000000000000000 / 4402162493639437579912510211376217659), (119993886180000000000000000000000000 / 1467387497879812526637503403792072553), (119994001346250000000000000000000000 / 1467387497879812526637503403792072553), (68229795647750000000000000000000000 / 4402162493639437579912510211376217659), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![2, 2, 0, 0, 0], ![7, 4, 4, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1465661656239 / 500000000000), (710005239919 / 1000000000000), (643775774107 / 250000000000), (355003476807 / 500000000000), (-1465661674607 / 500000000000)], ![(-934201373137 / 1000000000000), (-934200438119 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2083485535667 / 500000000000), (-2503798093347 / 1000000000000), (-125189856679 / 50000000000), (-2083484909613 / 500000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2931323312477 / 1000000000000), (8875065499 / 12500000000), (2575103096429 / 1000000000000), (142001390723 / 200000000000), (-2931323349213 / 1000000000000)], ![(-58387585821 / 62500000000), (-467100219059 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-4166971071333 / 1000000000000), (-1251899046673 / 500000000000), (-2503797133579 / 1000000000000), (-166678792769 / 40000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 5 31).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-1606499158633 / 200000000000), (-2195582277897 / 500000000000), (-2727992512867 / 1000000000000), (-862895435039 / 1000000000000), (-431447705143 / 500000000000), (-2727992331781 / 1000000000000), (-1756466381 / 400000000), (-2008123392457 / 250000000000)] : List ℚ).getD
    ((seed 5 31).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-2008123948291 / 250000000000), (-4391164555793 / 1000000000000), (-1363996256433 / 500000000000), (-431447717519 / 500000000000), (-172579082057 / 200000000000), (-136399616589 / 50000000000), (-4391165952499 / 1000000000000), (-8032493569827 / 1000000000000)] : List ℚ).getD
    ((seed 5 31).splits.idxOf (sourceShape 5 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 31) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 31 =>
        (splitWeight 5 31 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 31, ∏ i, weights i (c.val i) ≤ 1 := by
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
