-- Prove2me | solution 1 for mme_released_interior_owner2_cell19_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:37:02.959092+00:00
-- url     : https://prove2.me/submissions/2f56abe7-1104-4196-95cd-64ea8c7d580b

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 2 19 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(103801975659 / 250000000000), (6193081669 / 8000000000), (415208086583 / 1000000000000), (1 / 1), (1 / 1)], ![(66885039092500000000000000000000000 / 3391825333888489578792772914698460359), (138321484789000000000000000000000000 / 3391825333888489578792772914698460359), (66885068072500000000000000000000000 / 3391825333888489578792772914698460359), (1 / 1), (1 / 1)], ![(1947328533 / 50000000000), (1114393245773 / 500000000000), (8925146216413 / 500000000000), (1114393631099 / 500000000000), (38946570803 / 1000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-219743978497 / 250000000000), (-256008732503 / 1000000000000), (-175795094193 / 200000000000), (0 / 1), (0 / 1)], ![(-3926148190819 / 1000000000000), (-3199542926273 / 1000000000000), (-1963073878769 / 500000000000), (0 / 1), (0 / 1)], ![(-649112911043 / 200000000000), (20036431579 / 25000000000), (1441009945441 / 500000000000), (200364402233 / 250000000000), (-3245564551543 / 1000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-878975913987 / 1000000000000), (-128004366251 / 500000000000), (-219743867741 / 250000000000), (0 / 1), (0 / 1)], ![(-1963074095409 / 500000000000), (-49992858223 / 15625000000), (-3926147757537 / 1000000000000), (0 / 1), (0 / 1)], ![(-1622782277607 / 500000000000), (801457263161 / 1000000000000), (2882019890883 / 1000000000000), (801457608933 / 1000000000000), (-1622782275771 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 2 19).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-8050688654987 / 1000000000000), (-845174836011 / 250000000000), (-480775940999 / 250000000000), (-1638530602301 / 500000000000), (-286765883947 / 500000000000), (-3277061160801 / 1000000000000), (-961551893773 / 500000000000), (-1690349598617 / 500000000000), (-1006335972899 / 125000000000)] : List ℚ).getD
    ((seed 2 19).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-4025344327493 / 500000000000), (-3380699344043 / 1000000000000), (-384620752799 / 200000000000), (-3277061204601 / 1000000000000), (-573531767893 / 1000000000000), (-4096326451 / 1250000000), (-384620757509 / 200000000000), (-3380699197233 / 1000000000000), (-8050687783191 / 1000000000000)] : List ℚ).getD
    ((seed 2 19).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 2 19 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
