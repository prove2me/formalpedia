-- Prove2me | solution 1 for mme_released_interior_owner3_cell20_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T16:12:34.979044+00:00
-- url     : https://prove2.me/submissions/771781e3-10df-4b66-b009-fd8e87779217

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 3 20 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(27794373039 / 62500000000), (864192746609 / 1000000000000), (88932173967 / 200000000000), (1 / 1), (1 / 1)], ![(175563694793 / 1000000000000), (2352579894231 / 1000000000000), (588112508311 / 250000000000), (35106913673 / 200000000000), (1 / 1)], ![(168343754248000000000000000000000000 / 15913607759762020901079516007051635061), (2456397452732000000000000000000000000 / 15913607759762020901079516007051635061), (2456261940392000000000000000000000000 / 15913607759762020901079516007051635061), (168315640249000000000000000000000000 / 15913607759762020901079516007051635061), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![3, -1, -1, 3, 0], ![7, 3, 3, 7, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-810332965203 / 1000000000000), (-72979724353 / 500000000000), (-810443377613 / 1000000000000), (0 / 1), (0 / 1)], ![(-434938342157 / 250000000000), (213878138329 / 250000000000), (427728676199 / 500000000000), (-434979821183 / 250000000000), (0 / 1)], ![(-284307613189 / 62500000000), (-1868478750677 / 1000000000000), (-373706783861 / 200000000000), (-568636103561 / 125000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-405166482601 / 500000000000), (-29191889741 / 200000000000), (-202610844403 / 250000000000), (0 / 1), (0 / 1)], ![(-1739753368627 / 1000000000000), (855512553317 / 1000000000000), (855457352399 / 1000000000000), (-1739919284731 / 1000000000000), (0 / 1)], ![(-4548921811023 / 1000000000000), (-467119687669 / 250000000000), (-233566739913 / 125000000000), (-4549088828487 / 1000000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-3210521895491 / 500000000000), (-180236745127 / 40000000000), (-276286091219 / 62500000000), (-231810336849 / 200000000000), (-14243236679 / 7812500000), (-227891781507 / 125000000000), (-115905165209 / 100000000000), (-4420577120109 / 1000000000000), (-225296001559 / 50000000000), (-3210522452359 / 500000000000)] : List ℚ).getD
    ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-6421043790981 / 1000000000000), (-2252959314087 / 500000000000), (-4420577459503 / 1000000000000), (-289762921061 / 250000000000), (-1823134294911 / 1000000000000), (-364626850411 / 200000000000), (-1159051652089 / 1000000000000), (-1105144280027 / 250000000000), (-4505920031179 / 1000000000000), (-6421044904717 / 1000000000000)] : List ℚ).getD
    ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

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
        (splitWeight 3 20 0 c : ℝ) / 1000000000000) ≤
          (407 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (407 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((407 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
