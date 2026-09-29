-- Prove2me | solution 1 for mme_released_interior_owner2_cell13_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:15:57.502099+00:00
-- url     : https://prove2.me/submissions/67217a72-7ec3-4ac7-86f5-0e26ca70aef7

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 2 13 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(393311070971 / 1000000000000), (24581987529 / 62500000000), (1 / 1), (1 / 1), (1 / 1)], ![(53304936624000000000000000000000000 / 17575044366910268036191110652666565059), (2033839364311000000000000000000000000 / 17575044366910268036191110652666565059), (13159239901759000000000000000000000000 / 17575044366910268036191110652666565059), (2033845937943000000000000000000000000 / 17575044366910268036191110652666565059), (53304931710000000000000000000000000 / 17575044366910268036191110652666565059)], ![(54887918979 / 200000000000), (716430801829 / 500000000000), (358216095219 / 250000000000), (274439854907 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 2, 0, 0, 0], ![9, 4, 1, 4, 9], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-933154451019 / 1000000000000), (-933152596273 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-5798206294639 / 1000000000000), (-539138660721 / 250000000000), (-289355796123 / 1000000000000), (-53913785269 / 25000000000), (-2899103193413 / 500000000000)], ![(-323256024319 / 250000000000), (179836783067 / 500000000000), (89918876091 / 250000000000), (-161627893731 / 125000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-466577225509 / 500000000000), (-58322037267 / 62500000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2899103147319 / 500000000000), (-2156554642883 / 1000000000000), (-144677898061 / 500000000000), (-2156551410759 / 1000000000000), (-231928255473 / 40000000000)], ![(-51720963891 / 40000000000), (71934713227 / 200000000000), (71935100873 / 200000000000), (-1293023149847 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 13) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 2 13).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-8024382039271 / 1000000000000), (-2191366121859 / 500000000000), (-1365015867399 / 500000000000), (-862834742777 / 1000000000000), (-862834826261 / 1000000000000), (-2730032295647 / 1000000000000), (-4382728104327 / 1000000000000), (-2006096233743 / 250000000000)] : List ℚ).getD
    ((seed 2 13).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 13) : ℚ :=
  ([(-802438203927 / 100000000000), (-4382732243717 / 1000000000000), (-2730031734797 / 1000000000000), (-107854342847 / 125000000000), (-43141741313 / 50000000000), (-1365016147823 / 500000000000), (-2191364052163 / 500000000000), (-8024384934971 / 1000000000000)] : List ℚ).getD
    ((seed 2 13).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 13) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 13 =>
        (splitWeight 2 13 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 13, ∏ i, weights i (c.val i) ≤ 1 := by
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
