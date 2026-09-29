-- Prove2me | solution 1 for mme_released_interior_owner1_cell32_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:39.979253+00:00
-- url     : https://prove2.me/submissions/06f7c148-6571-4e5d-a535-f9ca9cfaf627

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 1 32 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(19466746576000000000000000000000000 / 9850206360499682457223367248514031603), (1174634089991000000000000000000000000 / 9850206360499682457223367248514031603), (920270426757500000000000000000000000 / 1094467373388853606358151916501559067), (391591183322500000000000000000000000 / 3283402120166560819074455749504677201), (19466871386000000000000000000000000 / 9850206360499682457223367248514031603)], ![(83436306559 / 200000000000), (396342572521 / 500000000000), (26076917563 / 62500000000), (1 / 1), (1 / 1)], ![(81526944701 / 200000000000), (830565154791 / 1000000000000), (407682734539 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 1, 2, 0, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-6226539978163 / 1000000000000), (-1063267859473 / 500000000000), (-173355537937 / 1000000000000), (-2126416999679 / 1000000000000), (-6226533566737 / 1000000000000)], ![(-874233821469 / 1000000000000), (-58082294753 / 250000000000), (-27316125571 / 31250000000), (0 / 1), (0 / 1)], ![(-897383791113 / 1000000000000), (-185648900519 / 1000000000000), (-897266018499 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3113269989081 / 500000000000), (-425307143789 / 200000000000), (-10834721121 / 62500000000), (-1063208499839 / 500000000000), (-389158347921 / 62500000000)], ![(-218558455367 / 250000000000), (-232329179011 / 1000000000000), (-874116018271 / 1000000000000), (0 / 1), (0 / 1)], ![(-112172973889 / 125000000000), (-92824450259 / 500000000000), (-448633009249 / 500000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 32) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-7997922014943 / 1000000000000), (-398287579659 / 125000000000), (-3256130916949 / 1000000000000), (-388971069491 / 200000000000), (-59133361747 / 100000000000), (-243106922221 / 125000000000), (-1628064984647 / 500000000000), (-796574930531 / 250000000000), (-7998151178811 / 1000000000000)] : List ℚ).getD
    ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 32) : ℚ :=
  ([(-3998961007471 / 500000000000), (-3186300637271 / 1000000000000), (-814032729237 / 250000000000), (-972427673727 / 500000000000), (-591333617469 / 1000000000000), (-1944855377767 / 1000000000000), (-3256129969293 / 1000000000000), (-3186299722123 / 1000000000000), (-7998151178809 / 1000000000000)] : List ℚ).getD
    ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 32 0 c : ℝ) / 1000000000000) ≤
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
