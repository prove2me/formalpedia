-- Prove2me | solution 1 for mme_released_interior_owner4_cell22_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T09:18:17.951433+00:00
-- url     : https://prove2.me/submissions/29ea3f5b-6ce1-4fcc-a169-51378e7e136e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 4 22 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(583022690231 / 1000000000000), (1051348914991 / 1000000000000), (145755479417 / 250000000000), (1 / 1), (1 / 1)], ![(1 / 1), (7799356371000000000000000000000000 / 380294663231394674075170425706699213), (191628166469300000000000000000000000 / 380294663231394674075170425706699213), (191628096466050000000000000000000000 / 380294663231394674075170425706699213), (7799348751750000000000000000000000 / 380294663231394674075170425706699213)], ![(119687900183 / 200000000000), (299219571 / 500000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![1, 0, 1, 0, 0], ![0, 6, 1, 1, 6], ![1, 1, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-539529173611 / 1000000000000), (6259252577 / 125000000000), (-539530498711 / 1000000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-777381033607 / 200000000000), (-68538952043 / 100000000000), (-342694942869 / 500000000000), (-3886906144943 / 1000000000000)], ![(-256714921807 / 500000000000), (-102686088673 / 200000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-53952917361 / 100000000000), (50074020617 / 1000000000000), (-53953049871 / 100000000000), (0 / 1), (0 / 1)], ![(0 / 1), (-1943452584017 / 500000000000), (-685389520429 / 1000000000000), (-685389885737 / 1000000000000), (-1943453072471 / 500000000000)], ![(-513429843613 / 1000000000000), (-128357610841 / 250000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 22) : ℤ :=
  ([8, 3, 2, 2, 3, 8] : List ℤ).getD
    ((seed 4 22).splits.idxOf (sourceShape 4 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-4939866110087 / 1000000000000), (-869174931377 / 500000000000), (-1148745943177 / 1000000000000), (-17949151699 / 15625000000), (-217293687839 / 125000000000), (-4939865162153 / 1000000000000)] : List ℚ).getD
    ((seed 4 22).splits.idxOf (sourceShape 4 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 22) : ℚ :=
  ([(-2469933055043 / 500000000000), (-1738349862753 / 1000000000000), (-143593242897 / 125000000000), (-229749141747 / 200000000000), (-1738349502711 / 1000000000000), (-617483145269 / 125000000000)] : List ℚ).getD
    ((seed 4 22).splits.idxOf (sourceShape 4 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 22) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 22 =>
        (splitWeight 4 22 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 22, ∏ i, weights i (c.val i) ≤ 1 := by
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
