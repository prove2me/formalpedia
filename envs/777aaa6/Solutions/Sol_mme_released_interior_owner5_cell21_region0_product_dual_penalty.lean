-- Prove2me | solution 1 for mme_released_interior_owner5_cell21_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:22:47.480741+00:00
-- url     : https://prove2.me/submissions/061d569d-51fa-4393-a6b6-1193fba1f6b0

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 5 21 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(418479487059 / 1000000000000), (194238253281 / 250000000000), (104616623757 / 250000000000), (1 / 1), (1 / 1)], ![(194848301 / 5000000000), (2292017507969 / 1000000000000), (17108392727589 / 1000000000000), (572986296843 / 250000000000), (7793926779 / 200000000000)], ![(2797016403000000000000000000000000 / 138717256815637478041077111556521037), (5825855480500000000000000000000000 / 138717256815637478041077111556521037), (25172380388000000000000000000000000 / 1248455311340737302369694004008689333), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![5, -1, -4, -1, 5], ![6, 5, 6, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-174225481129 / 200000000000), (-252375402613 / 1000000000000), (-108894806491 / 125000000000), (0 / 1), (0 / 1)], ![(-1622485939599 / 500000000000), (829432437553 / 1000000000000), (2839569145887 / 1000000000000), (829400883807 / 1000000000000), (-324497255421 / 100000000000)], ![(-3903884459163 / 1000000000000), (-317013188559 / 100000000000), (-3903914938097 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-217781851411 / 250000000000), (-63093850653 / 250000000000), (-871158451927 / 1000000000000), (0 / 1), (0 / 1)], ![(-3244971879197 / 1000000000000), (414716218777 / 500000000000), (88736535809 / 31250000000), (25918777619 / 31250000000), (-3244972554209 / 1000000000000)], ![(-1951942229581 / 500000000000), (-3170131885589 / 1000000000000), (-243994683631 / 62500000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 5 21).splits.idxOf (sourceShape 5 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-1935473776303 / 1000000000000), (-831714733331 / 250000000000), (-1603996883921 / 200000000000), (-100370558131 / 31250000000), (-291469071159 / 500000000000), (-401482305901 / 125000000000), (-250626414637 / 31250000000), (-3326857947771 / 1000000000000), (-1935473186753 / 1000000000000)] : List ℚ).getD
    ((seed 5 21).splits.idxOf (sourceShape 5 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-967736888151 / 500000000000), (-3326858933323 / 1000000000000), (-2004996104901 / 250000000000), (-3211857860191 / 1000000000000), (-582938142317 / 1000000000000), (-3211858447207 / 1000000000000), (-8020045268383 / 1000000000000), (-332685794777 / 100000000000), (-30241768543 / 15625000000)] : List ℚ).getD
    ((seed 5 21).splits.idxOf (sourceShape 5 c)) 0

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
        (splitWeight 5 21 0 c : ℝ) / 1000000000000) ≤
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
