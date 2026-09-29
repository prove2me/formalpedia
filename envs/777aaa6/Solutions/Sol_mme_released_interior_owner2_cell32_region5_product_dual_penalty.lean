-- Prove2me | solution 1 for mme_released_interior_owner2_cell32_region5_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:50:55.557448+00:00
-- url     : https://prove2.me/submissions/5413674e-66b1-4df6-a737-e97a832fc2a4

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 2 32 5 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(39025052959 / 1000000000000), (2333008384237 / 1000000000000), (16631443998837 / 1000000000000), (466592183373 / 200000000000), (7805007361 / 200000000000)], ![(5254336434300000000000000000000000 / 246652630189939043058393564839472119), (9741720554812500000000000000000000 / 246652630189939043058393564839472119), (5254230570175000000000000000000000 / 246652630189939043058393564839472119), (1 / 1), (1 / 1)], ![(403849592041 / 1000000000000), (211152151057 / 250000000000), (403841462107 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![5, -1, -4, -1, 5], ![6, 5, 6, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-3243551455529 / 1000000000000), (84715858679 / 100000000000), (2811295120393 / 1000000000000), (84713824059 / 100000000000), (-810887967367 / 250000000000)], ![(-3848927268127 / 1000000000000), (-807890810221 / 250000000000), (-3848947416283 / 1000000000000), (0 / 1), (0 / 1)], ![(-906712767269 / 1000000000000), (-84440974597 / 500000000000), (-453366449283 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-405443931941 / 125000000000), (847158586791 / 1000000000000), (1405647560197 / 500000000000), (847138240591 / 1000000000000), (-3243551869467 / 1000000000000)], ![(-1924463634063 / 500000000000), (-3231563240883 / 1000000000000), (-1924473708141 / 500000000000), (0 / 1), (0 / 1)], ![(-226678191817 / 250000000000), (-168881949193 / 1000000000000), (-181346579713 / 200000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([3, 5, 12, 5, 1, 5, 12, 5, 3] : List ℤ).getD
    ((seed 2 32).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-972182528733 / 500000000000), (-3170670938679 / 1000000000000), (-1599838381081 / 200000000000), (-1645568754863 / 500000000000), (-294575034841 / 500000000000), (-3291137810493 / 1000000000000), (-3999615885557 / 500000000000), (-3170670816751 / 1000000000000), (-1944365051993 / 1000000000000)] : List ℚ).getD
    ((seed 2 32).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-388873011493 / 200000000000), (-1585335469339 / 500000000000), (-1999797976351 / 250000000000), (-131645500389 / 40000000000), (-589150069681 / 1000000000000), (-822784452623 / 250000000000), (-7999231771113 / 1000000000000), (-12682683267 / 4000000000), (-243045631499 / 125000000000)] : List ℚ).getD
    ((seed 2 32).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 32) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 32 =>
        (splitWeight 2 32 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 32, ∏ i, weights i (c.val i) ≤ 1 := by
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
