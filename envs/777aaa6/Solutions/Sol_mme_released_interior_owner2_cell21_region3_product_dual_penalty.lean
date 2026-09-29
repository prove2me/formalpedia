-- Prove2me | solution 1 for mme_released_interior_owner2_cell21_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:16.959994+00:00
-- url     : https://prove2.me/submissions/b6a525d4-58a3-460f-9f6d-6fa4816c0efd

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 2 21 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(411052718363 / 1000000000000), (81063565223 / 100000000000), (102752244347 / 250000000000), (1 / 1), (1 / 1)], ![(38992334124000000000000000000000000 / 19830555014336130908850027488138034257), (2311107208797000000000000000000000000 / 19830555014336130908850027488138034257), (16883652369142000000000000000000000000 / 19830555014336130908850027488138034257), (2310859150886000000000000000000000000 / 19830555014336130908850027488138034257), (38992233669000000000000000000000000 / 19830555014336130908850027488138034257)], ![(82585983041 / 200000000000), (804512924153 / 1000000000000), (8257719461 / 20000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![9, 4, 1, 4, 9], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-889033804189 / 1000000000000), (-209936583237 / 1000000000000), (-222285055483 / 250000000000), (0 / 1), (0 / 1)], ![(-6231614143857 / 1000000000000), (-537374302473 / 250000000000), (-80439046209 / 500000000000), (-268700568573 / 125000000000), (-778952090017 / 125000000000)], ![(-442238698631 / 500000000000), (-217518247853 / 1000000000000), (-884583818453 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-222258451047 / 250000000000), (-52484145809 / 250000000000), (-889140221931 / 1000000000000), (0 / 1), (0 / 1)], ![(-389475883991 / 62500000000), (-2149497209891 / 1000000000000), (-160878092417 / 1000000000000), (-2149604548583 / 1000000000000), (-1246323344027 / 200000000000)], ![(-884477397261 / 1000000000000), (-54379561963 / 250000000000), (-221145954613 / 250000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-250166818239 / 31250000000), (-324401761737 / 100000000000), (-162807783691 / 50000000000), (-967247856749 / 500000000000), (-294166461753 / 500000000000), (-483623928293 / 250000000000), (-130246264259 / 40000000000), (-1622009261657 / 500000000000), (-800512792133 / 100000000000)] : List ℚ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8005338183647 / 1000000000000), (-3244017617369 / 1000000000000), (-3256155673819 / 1000000000000), (-1934495713497 / 1000000000000), (-117666584701 / 200000000000), (-1934495713171 / 1000000000000), (-1628078303237 / 500000000000), (-3244018523313 / 1000000000000), (-8005127921329 / 1000000000000)] : List ℚ).getD
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
        (splitWeight 2 21 3 c : ℝ) / 1000000000000) ≤
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
