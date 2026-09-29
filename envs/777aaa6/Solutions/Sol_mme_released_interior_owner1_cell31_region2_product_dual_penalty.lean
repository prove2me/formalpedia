-- Prove2me | solution 1 for mme_released_interior_owner1_cell31_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:37.384393+00:00
-- url     : https://prove2.me/submissions/38f323b4-4374-4c74-803c-4ed1e04d8778

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 1 31 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(26663402521500000000000000000000000 / 8804938143076705583727326116203811579), (1017121275657500000000000000000000000 / 8804938143076705583727326116203811579), (6566437652948000000000000000000000000 / 8804938143076705583727326116203811579), (1017117883950000000000000000000000000 / 8804938143076705583727326116203811579), (26663401577500000000000000000000000 / 8804938143076705583727326116203811579)], ![(12277738243 / 31250000000), (392886916239 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(272901684593 / 1000000000000), (1440034754641 / 1000000000000), (57601283179 / 40000000000), (272900968367 / 1000000000000), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 2, 0, 0, 0], ![2, 0, 0, 2, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-724972007829 / 125000000000), (-2158336358329 / 1000000000000), (-146670622719 / 500000000000), (-2158339692949 / 1000000000000), (-1449944024509 / 250000000000)], ![(-467115826297 / 500000000000), (-934233453459 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-324660919589 / 250000000000), (22791703029 / 62500000000), (11395793461 / 31250000000), (-1298646302843 / 1000000000000), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-5799776062631 / 1000000000000), (-269792044791 / 125000000000), (-293341245437 / 1000000000000), (-539584923237 / 250000000000), (-1159955219607 / 200000000000)], ![(-934231652593 / 1000000000000), (-467116726729 / 500000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-259728735671 / 200000000000), (72933449693 / 200000000000), (364665390753 / 1000000000000), (-649323151421 / 500000000000), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 31) : ℤ :=
  ([12, 4, 7, 2, 2, 7, 4, 12] : List ℤ).getD
    ((seed 1 31).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-803265581867 / 100000000000), (-1363952210521 / 500000000000), (-2195607156897 / 500000000000), (-86290745043 / 100000000000), (-431453753639 / 500000000000), (-4391216824761 / 1000000000000), (-1363952048539 / 500000000000), (-8032651429807 / 1000000000000)] : List ℚ).getD
    ((seed 1 31).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 31) : ℚ :=
  ([(-8032655818669 / 1000000000000), (-2727904421041 / 1000000000000), (-4391214313793 / 1000000000000), (-862907450429 / 1000000000000), (-862907507277 / 1000000000000), (-109780420619 / 25000000000), (-2727904097077 / 1000000000000), (-4016325714903 / 500000000000)] : List ℚ).getD
    ((seed 1 31).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 31 2 c : ℝ) / 1000000000000) ≤
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
