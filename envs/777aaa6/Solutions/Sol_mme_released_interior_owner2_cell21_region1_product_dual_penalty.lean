-- Prove2me | solution 1 for mme_released_interior_owner2_cell21_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:15.201907+00:00
-- url     : https://prove2.me/submissions/b6b615a9-035f-416c-bcd3-45736ce9556e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 2 21 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(83141093361 / 200000000000), (394294804787 / 500000000000), (415756140401 / 1000000000000), (1 / 1), (1 / 1)], ![(38844016556000000000000000000000000 / 19955190033889100514196498947378421019), (2309199265339000000000000000000000000 / 19955190033889100514196498947378421019), (17063252408127000000000000000000000000 / 19955190033889100514196498947378421019), (2309483177732000000000000000000000000 / 19955190033889100514196498947378421019), (38844223895000000000000000000000000 / 19955190033889100514196498947378421019)], ![(405949510563 / 1000000000000), (413100250521 / 500000000000), (81199798391 / 200000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![10, 4, 1, 4, 10], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-877778281969 / 1000000000000), (-237509233413 / 1000000000000), (-877656391563 / 1000000000000), (0 / 1), (0 / 1)], ![(-624169048961 / 100000000000), (-1078294217759 / 500000000000), (-6262483697 / 40000000000), (-2156465494659 / 1000000000000), (-6241685151891 / 1000000000000)], ![(-901526485333 / 1000000000000), (-190917797579 / 1000000000000), (-901404602253 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-54861142623 / 62500000000), (-59377308353 / 250000000000), (-438828195781 / 500000000000), (0 / 1), (0 / 1)], ![(-6241690489609 / 1000000000000), (-2156588435517 / 1000000000000), (-19570261553 / 125000000000), (-1078232747329 / 500000000000), (-624168515189 / 100000000000)], ![(-225381621333 / 250000000000), (-95458898789 / 500000000000), (-225351150563 / 250000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8020751482941 / 1000000000000), (-3295502271353 / 1000000000000), (-645032524899 / 200000000000), (-9678724883 / 5000000000), (-73123640427 / 125000000000), (-387148993873 / 200000000000), (-645032314873 / 200000000000), (-3295501213227 / 1000000000000), (-1604197984217 / 200000000000)] : List ℚ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-401037574147 / 50000000000), (-411937783919 / 125000000000), (-1612581312247 / 500000000000), (-1935744976599 / 1000000000000), (-116997824683 / 200000000000), (-483936242341 / 250000000000), (-806290393591 / 250000000000), (-1647750606613 / 500000000000), (-2005247480271 / 250000000000)] : List ℚ).getD
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
        (splitWeight 2 21 1 c : ℝ) / 1000000000000) ≤
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
