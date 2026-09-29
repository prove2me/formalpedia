-- Prove2me | solution 1 for mme_released_interior_owner2_cell20_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:12.431811+00:00
-- url     : https://prove2.me/submissions/cd81c097-64c7-497d-8475-9319c530f942

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 2 20 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(2217650817 / 5000000000), (849006012821 / 1000000000000), (443471352169 / 1000000000000), (1 / 1), (1 / 1)], ![(82335592834000000000000000000000000 / 8126894476117990195560195297211273417), (1242191462831000000000000000000000000 / 8126894476117990195560195297211273417), (1242109207831500000000000000000000000 / 8126894476117990195560195297211273417), (82319009914500000000000000000000000 / 8126894476117990195560195297211273417), (1 / 1)], ![(84807489147 / 500000000000), (241065387957 / 100000000000), (1205246950301 / 500000000000), (169581524179 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-81298946737 / 100000000000), (-163689010457 / 1000000000000), (-813122074203 / 1000000000000), (0 / 1), (0 / 1)], ![(-22960653277 / 5000000000), (-187830173883 / 100000000000), (-117397997417 / 62500000000), (-918466416427 / 200000000000), (0 / 1)], ![(-110889015257 / 62500000000), (35195921201 / 40000000000), (439915832257 / 500000000000), (-1774421499183 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-812989467369 / 1000000000000), (-20461126307 / 125000000000), (-406561037101 / 500000000000), (0 / 1), (0 / 1)], ![(-4592130655399 / 1000000000000), (-1878301738829 / 1000000000000), (-1878367958671 / 1000000000000), (-2296166041067 / 500000000000), (0 / 1)], ![(-1774224244111 / 1000000000000), (439949015013 / 500000000000), (175966332903 / 200000000000), (-887210749591 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 20) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 2 20).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-1625291924271 / 250000000000), (-4529402203301 / 1000000000000), (-893892532107 / 200000000000), (-1162296655199 / 1000000000000), (-1810999246971 / 1000000000000), (-905499612751 / 500000000000), (-1162296510053 / 1000000000000), (-4469464223207 / 1000000000000), (-4529404651779 / 1000000000000), (-1300234372483 / 200000000000)] : List ℚ).getD
    ((seed 2 20).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 20) : ℚ :=
  ([(-6501167697083 / 1000000000000), (-45294022033 / 10000000000), (-2234731330267 / 500000000000), (-581148327599 / 500000000000), (-181099924697 / 100000000000), (-1810999225501 / 1000000000000), (-290574127513 / 250000000000), (-2234732111603 / 500000000000), (-2264702325889 / 500000000000), (-3250585931207 / 500000000000)] : List ℚ).getD
    ((seed 2 20).splits.idxOf (sourceShape 2 c)) 0

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
        (splitWeight 2 20 1 c : ℝ) / 1000000000000) ≤
          (1641 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 20, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (1641 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1641 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
