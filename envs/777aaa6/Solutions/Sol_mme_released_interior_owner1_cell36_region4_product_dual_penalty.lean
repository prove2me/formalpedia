-- Prove2me | solution 1 for mme_released_interior_owner1_cell36_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:45.814889+00:00
-- url     : https://prove2.me/submissions/ebe818c2-80c0-48c5-98f0-7fd08ba9ef2e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 1 36 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(1 / 1), (3938615587525000000000000000000000 / 188996555868819812697970056013695511), (95154429392950000000000000000000000 / 188996555868819812697970056013695511), (95154336977325000000000000000000000 / 188996555868819812697970056013695511), (3938612684100000000000000000000000 / 188996555868819812697970056013695511)], ![(149911952519 / 250000000000), (599647173159 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(586448506647 / 1000000000000), (104542567119 / 100000000000), (586447312709 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-3870899504139 / 1000000000000), (-686227647633 / 1000000000000), (-686228618851 / 1000000000000), (-967725060327 / 250000000000)], ![(-102282555863 / 200000000000), (-127853460367 / 250000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-533670412447 / 1000000000000), (44424143327 / 1000000000000), (-66709056041 / 125000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(0 / 1), (-1935449752069 / 500000000000), (-42889227977 / 62500000000), (-13724572377 / 20000000000), (-3870900241307 / 1000000000000)], ![(-255706389657 / 500000000000), (-511413841467 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-266835206223 / 500000000000), (1388254479 / 31250000000), (-533672448327 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 36) : ℤ :=
  ([8, 2, 3, 3, 2, 8] : List ℤ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-4915985793993 / 1000000000000), (-288304336443 / 250000000000), (-69252515011 / 40000000000), (-865656436381 / 500000000000), (-1153217254837 / 1000000000000), (-4915983433073 / 1000000000000)] : List ℚ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 36) : ℚ :=
  ([(-614498224249 / 125000000000), (-1153217345771 / 1000000000000), (-865656437637 / 500000000000), (-1731312872761 / 1000000000000), (-288304313709 / 250000000000), (-307248964567 / 62500000000)] : List ℚ).getD
    ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 36) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 1 36 4 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 36, ∏ i, weights i (c.val i) ≤ 1 := by
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
