-- Prove2me | solution 1 for mme_released_interior_owner2_cell27_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:44:29.861982+00:00
-- url     : https://prove2.me/submissions/81453c3f-1f3e-440d-b800-f1bccd68c631

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 2 27 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(85613804683 / 500000000000), (598569814427 / 250000000000), (239438216467 / 100000000000), (34250131149 / 200000000000), (1 / 1)], ![(82472627640500000000000000000000000 / 8092964264352042136271409936188793611), (1243485847994000000000000000000000000 / 8092964264352042136271409936188793611), (1243539732037000000000000000000000000 / 8092964264352042136271409936188793611), (82482853524500000000000000000000000 / 8092964264352042136271409936188793611), (1 / 1)], ![(443873933087 / 1000000000000), (53122564461 / 62500000000), (443912243429 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![3, -1, -1, 3, 0], ![7, 3, 3, 7, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-220595194827 / 125000000000), (873082249333 / 1000000000000), (21828130719 / 25000000000), (-44115674317 / 25000000000), (0 / 1)], ![(-18345135607 / 4000000000), (-468269117867 / 250000000000), (-37460662787 / 20000000000), (-4586159918189 / 1000000000000), (0 / 1)], ![(-203053672839 / 250000000000), (-162564775989 / 1000000000000), (-40606419301 / 50000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-352952311723 / 200000000000), (436541124667 / 500000000000), (873125228761 / 1000000000000), (-1764626972679 / 1000000000000), (0 / 1)], ![(-4586283901749 / 1000000000000), (-1873076471467 / 1000000000000), (-1873033139349 / 1000000000000), (-1146539979547 / 250000000000), (0 / 1)], ![(-162442938271 / 200000000000), (-40641193997 / 250000000000), (-812128386019 / 1000000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([7, 10, 3, 2, 7, 7, 2, 3, 10, 7] : List ℤ).getD
    ((seed 2 27).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-4529235140821 / 1000000000000), (-3242554303797 / 500000000000), (-1811600054277 / 1000000000000), (-1162652515169 / 1000000000000), (-556697383291 / 125000000000), (-1113395998921 / 250000000000), (-581326081909 / 500000000000), (-1811600048071 / 1000000000000), (-6485119198117 / 1000000000000), (-2264620211413 / 500000000000)] : List ℚ).getD
    ((seed 2 27).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-226461757041 / 50000000000), (-6485108607593 / 1000000000000), (-452900013569 / 250000000000), (-36332891099 / 31250000000), (-4453579066327 / 1000000000000), (-4453583995683 / 1000000000000), (-1162652163817 / 1000000000000), (-181160004807 / 100000000000), (-1621279799529 / 250000000000), (-181169616913 / 40000000000)] : List ℚ).getD
    ((seed 2 27).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 2 27 0 c : ℝ) / 1000000000000) ≤
          (1592 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1592 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1592 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
