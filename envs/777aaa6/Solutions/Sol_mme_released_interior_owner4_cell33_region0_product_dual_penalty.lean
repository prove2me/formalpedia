-- Prove2me | solution 1 for mme_released_interior_owner4_cell33_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:19:24.605836+00:00
-- url     : https://prove2.me/submissions/acd45e11-1a38-4c39-9f30-ce20aa1994d0

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 4 33 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(5339849433 / 100000000000), (82652750561 / 40000000000), (6390442445271 / 500000000000), (2066320371193 / 1000000000000), (26699247069 / 500000000000)], ![(45354091618000000000000000000000000 / 2908730159889233998758634018853005421), (725148079426000000000000000000000000 / 8726190479667701996275902056559016263), (725148386225000000000000000000000000 / 8726190479667701996275902056559016263), (136062361598500000000000000000000000 / 8726190479667701996275902056559016263), (1 / 1)], ![(197338685727 / 500000000000), (394677534957 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![7, 4, 4, 7, 0], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-2929972729481 / 1000000000000), (90721081153 / 125000000000), (2547950686813 / 1000000000000), (90721178377 / 125000000000), (-2929972733077 / 1000000000000)], ![(-1040242874539 / 250000000000), (-2487708300941 / 1000000000000), (-2487707877857 / 1000000000000), (-4160970860621 / 1000000000000), (0 / 1)], ![(-464843314479 / 500000000000), (-29052694209 / 31250000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-73249318237 / 25000000000), (29030745969 / 40000000000), (1273975343407 / 500000000000), (725769427017 / 1000000000000), (-732493183269 / 250000000000)], ![(-832194299631 / 200000000000), (-124385415047 / 50000000000), (-77740871183 / 31250000000), (-208048543031 / 50000000000), (0 / 1)], ![(-929686628957 / 1000000000000), (-929686214687 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 4 33).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-8020630859493 / 1000000000000), (-436488828581 / 100000000000), (-538325100577 / 200000000000), (-173888765763 / 200000000000), (-434721910001 / 500000000000), (-672906360829 / 250000000000), (-68201388131 / 15625000000), (-8020629803539 / 1000000000000)] : List ℚ).getD
    ((seed 4 33).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-2005157714873 / 250000000000), (-4364888285809 / 1000000000000), (-672906375721 / 250000000000), (-434721914407 / 500000000000), (-869443820001 / 1000000000000), (-538325088663 / 200000000000), (-4364888840383 / 1000000000000), (-4010314901769 / 500000000000)] : List ℚ).getD
    ((seed 4 33).splits.idxOf (sourceShape 4 c)) 0

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
        (splitWeight 4 33 0 c : ℝ) / 1000000000000) ≤
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
