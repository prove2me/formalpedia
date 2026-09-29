-- Prove2me | solution 1 for mme_released_interior_owner2_cell21_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:18.19074+00:00
-- url     : https://prove2.me/submissions/6445ae68-dc68-43cd-8f80-d101dd9b058c

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 2 21 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(103147869071 / 250000000000), (25167882983 / 31250000000), (206272965263 / 500000000000), (1 / 1), (1 / 1)], ![(9747658155000000000000000000000000 / 4957851711792431966126567014148509867), (577813354863000000000000000000000000 / 4957851711792431966126567014148509867), (4221344217929000000000000000000000000 / 4957851711792431966126567014148509867), (577749031999250000000000000000000000 / 4957851711792431966126567014148509867), (9747631139500000000000000000000000 / 4957851711792431966126567014148509867)], ![(411373916219 / 1000000000000), (161945051293 / 200000000000), (411328505173 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![9, 4, 1, 4, 9], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-177059467421 / 200000000000), (-108225339657 / 500000000000), (-885407732677 / 1000000000000), (0 / 1), (0 / 1)], ![(-6231700736343 / 1000000000000), (-214947690221 / 100000000000), (-160818911909 / 1000000000000), (-1074794114793 / 500000000000), (-6231703507833 / 1000000000000)], ![(-55515794141 / 62500000000), (-211060278403 / 1000000000000), (-888363101083 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-55331083569 / 62500000000), (-216450679313 / 1000000000000), (-221351933169 / 250000000000), (0 / 1), (0 / 1)], ![(-3115850368171 / 500000000000), (-2149476902209 / 1000000000000), (-40204727977 / 250000000000), (-429917645917 / 200000000000), (-778962938479 / 125000000000)], ![(-177650541251 / 200000000000), (-105530139201 / 500000000000), (-444181550541 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-31271373321 / 3906250000), (-3254290685027 / 1000000000000), (-3245944910881 / 1000000000000), (-38689586989 / 20000000000), (-294164934813 / 500000000000), (-386895870297 / 200000000000), (-649189169499 / 200000000000), (-813572903183 / 250000000000), (-8005253551397 / 1000000000000)] : List ℚ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-320218862807 / 40000000000), (-1627145342513 / 500000000000), (-20287155693 / 6250000000), (-1934479349449 / 1000000000000), (-4706638957 / 8000000000), (-483619837871 / 250000000000), (-1622972923747 / 500000000000), (-3254291612731 / 1000000000000), (-2001313387849 / 250000000000)] : List ℚ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 21 5 c : ℝ) / 1000000000000) ≤
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
