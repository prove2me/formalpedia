-- Prove2me | solution 1 for mme_released_interior_owner1_cell21_region1_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T12:44:52.759741+00:00
-- url     : https://prove2.me/submissions/137375c7-f88a-42f6-a2ce-a0977c77d10e

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 1 21 1 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(67079043526000000000000000000000000 / 3329674968651905700914714997521225623), (420226792762000000000000000000000000 / 9989024905955717102744144992563676869), (201236682614500000000000000000000000 / 9989024905955717102744144992563676869), (1 / 1), (1 / 1)], ![(19482297977 / 500000000000), (1146061952511 / 500000000000), (8557188619077 / 500000000000), (1146059388539 / 500000000000), (4870574309 / 125000000000)], ![(209352953859 / 500000000000), (96922527987 / 125000000000), (418704971427 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-976189573263 / 250000000000), (-1584223855781 / 500000000000), (-3904760519103 / 1000000000000), (0 / 1), (0 / 1)], ![(-3245101841201 / 1000000000000), (414739428587 / 500000000000), (2839918884417 / 1000000000000), (829476619969 / 1000000000000), (-649020375847 / 200000000000)], ![(-870586496389 / 1000000000000), (-254401758461 / 1000000000000), (-435294366273 / 500000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-3904758293051 / 1000000000000), (-3168447711561 / 1000000000000), (-1952380259551 / 500000000000), (0 / 1), (0 / 1)], ![(-8112754603 / 2500000000), (33179154287 / 40000000000), (1419959442209 / 500000000000), (82947661997 / 100000000000), (-1622550939617 / 500000000000)], ![(-217646624097 / 250000000000), (-12720087923 / 50000000000), (-174117746509 / 200000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8020446668697 / 1000000000000), (-166484172829 / 50000000000), (-1935428134971 / 1000000000000), (-641911513157 / 200000000000), (-116586117121 / 200000000000), (-3209557609129 / 1000000000000), (-387085627457 / 200000000000), (-1664841697679 / 500000000000), (-1604090218511 / 200000000000)] : List ℚ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-1002555833587 / 125000000000), (-3329683456579 / 1000000000000), (-193542813497 / 100000000000), (-401194695723 / 125000000000), (-145732646401 / 250000000000), (-401194701141 / 125000000000), (-483857034321 / 250000000000), (-3329683395357 / 1000000000000), (-8020451092553 / 1000000000000)] : List ℚ).getD
    ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

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
        (splitWeight 1 21 1 c : ℝ) / 1000000000000) ≤
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
