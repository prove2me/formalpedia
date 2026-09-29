-- Prove2me | solution 1 for mme_released_interior_owner0_cell20_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:25:26.766014+00:00
-- url     : https://prove2.me/submissions/d678b5f5-c7d4-4bd6-b7c7-3985b64b97d7

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 0 20 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(55563339121750000000000000000000000 / 1989754610221682914605929360945352497), (107979883247000000000000000000000000 / 1989754610221682914605929360945352497), (55557097452125000000000000000000000 / 1989754610221682914605929360945352497), (1 / 1), (1 / 1)], ![(84469398407 / 500000000000), (489973839789 / 200000000000), (97989128779 / 40000000000), (5278693463 / 31250000000), (1 / 1)], ![(175007274053 / 1000000000000), (2360566783823 / 1000000000000), (472087549747 / 200000000000), (174970500759 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![3, -1, -1, 3, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-715648596641 / 200000000000), (-1456910827563 / 500000000000), (-357835532383 / 100000000000), (0 / 1), (0 / 1)], ![(-1778218778681 / 1000000000000), (179206926989 / 200000000000), (111997135947 / 125000000000), (-71133630371 / 40000000000), (0 / 1)], ![(-871463869953 / 500000000000), (858901752839 / 1000000000000), (858847088589 / 1000000000000), (-43578447159 / 25000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-894560745801 / 250000000000), (-23310573241 / 8000000000), (-3578355323829 / 1000000000000), (0 / 1), (0 / 1)], ![(-44455469467 / 25000000000), (448017317473 / 500000000000), (895977087577 / 1000000000000), (-889170379637 / 500000000000), (0 / 1)], ![(-348585547981 / 200000000000), (21472543821 / 25000000000), (85884708859 / 100000000000), (-1743137886359 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([7, 3, 7, 10, 2, 2, 10, 7, 3, 7] : List ℤ).getD
    ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-4427190734839 / 1000000000000), (-911572807597 / 500000000000), (-562458148931 / 125000000000), (-1605380228877 / 250000000000), (-231802046287 / 200000000000), (-1159013107783 / 1000000000000), (-16053581499 / 2500000000), (-4499710108207 / 1000000000000), (-364629148833 / 200000000000), (-2213575292593 / 500000000000)] : List ℚ).getD
    ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-2213595367419 / 500000000000), (-1823145615193 / 1000000000000), (-4499665191447 / 1000000000000), (-6421520915507 / 1000000000000), (-579505115717 / 500000000000), (-579506553891 / 500000000000), (-6421432599599 / 1000000000000), (-2249855054103 / 500000000000), (-455786436041 / 250000000000), (-885430117037 / 200000000000)] : List ℚ).getD
    ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 20) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 0 20 2 c : ℝ) / 1000000000000) ≤
          (400 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (400 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((400 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
