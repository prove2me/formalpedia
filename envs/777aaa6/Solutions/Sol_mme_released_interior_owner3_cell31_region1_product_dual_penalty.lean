-- Prove2me | solution 1 for mme_released_interior_owner3_cell31_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T17:12:35.741186+00:00
-- url     : https://prove2.me/submissions/ed569ac1-d3c5-42a2-b51c-2c7c1102eaef

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 3 31 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(26698629717 / 500000000000), (1033025736819 / 500000000000), (6388112036033 / 500000000000), (16140938467 / 7812500000), (53397250173 / 1000000000000)], ![(394514021109 / 1000000000000), (197256511971 / 500000000000), (1 / 1), (1 / 1), (1 / 1)], ![(22629523952000000000000000000000000 / 1455594387651050582767534447639402559), (363186444086750000000000000000000000 / 4366783162953151748302603342918207677), (363185549762500000000000000000000000 / 4366783162953151748302603342918207677), (67887791742500000000000000000000000 / 4366783162953151748302603342918207677), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -3, -1, 5], ![2, 2, 0, 0, 0], ![7, 4, 4, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1464997927897 / 500000000000), (725639285023 / 1000000000000), (2547585949273 / 1000000000000), (45352111969 / 62500000000), (-292999602923 / 100000000000)], ![(-930100597861 / 1000000000000), (-930103125447 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-4163914186759 / 1000000000000), (-77714549257 / 31250000000), (-497373607733 / 200000000000), (-520490709739 / 125000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2929995855793 / 1000000000000), (22676227657 / 31250000000), (1273792974637 / 500000000000), (145126758301 / 200000000000), (-2929996029229 / 1000000000000)], ![(-46505029893 / 50000000000), (-465051562723 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2081957093379 / 500000000000), (-2486865576223 / 1000000000000), (-310858504833 / 125000000000), (-4163925677911 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([7, 12, 2, 4, 4, 2, 12, 7] : List ℤ).getD
    ((seed 3 31).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-1092095880181 / 250000000000), (-1003001351801 / 125000000000), (-869382752397 / 1000000000000), (-2691332382573 / 1000000000000), (-336416484887 / 125000000000), (-869382687251 / 1000000000000), (-8024024658617 / 1000000000000), (-4368386990743 / 1000000000000)] : List ℚ).getD
    ((seed 3 31).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-4368383520723 / 1000000000000), (-8024010814407 / 1000000000000), (-217345688099 / 250000000000), (-672833095643 / 250000000000), (-538266375819 / 200000000000), (-3477530749 / 4000000000), (-1003003082327 / 125000000000), (-2184193495371 / 500000000000)] : List ℚ).getD
    ((seed 3 31).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 31 1 c : ℝ) / 1000000000000) ≤
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
