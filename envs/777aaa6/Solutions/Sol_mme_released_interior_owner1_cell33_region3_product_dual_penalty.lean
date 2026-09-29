-- Prove2me | solution 1 for mme_released_interior_owner1_cell33_region3_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:42.485736+00:00
-- url     : https://prove2.me/submissions/058782cb-cae3-46de-a998-423913d375d9

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 1 33 3 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(6676687378625000000000000000000000 / 2178673863485662755018120462897578019), (258264994132750000000000000000000000 / 2178673863485662755018120462897578019), (1596804112834000000000000000000000000 / 2178673863485662755018120462897578019), (86088350904125000000000000000000000 / 726224621161887585006040154299192673), (6676687255750000000000000000000000 / 2178673863485662755018120462897578019)], ![(272732260837 / 1000000000000), (1447865547239 / 1000000000000), (90491615523 / 62500000000), (3409149889 / 12500000000), (1 / 1)], ![(394952120237 / 1000000000000), (394952194567 / 1000000000000), (1 / 1), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![9, 4, 1, 4, 9], ![2, 0, 0, 2, 0], ![2, 2, 0, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-1157569937607 / 200000000000), (-2132485484333 / 1000000000000), (-155356084977 / 500000000000), (-2132485257513 / 1000000000000), (-5787849706439 / 1000000000000)], ![(-649632347281 / 500000000000), (74018087107 / 200000000000), (92522660879 / 250000000000), (-1299265683507 / 1000000000000), (0 / 1)], ![(-464495368009 / 500000000000), (-464495273909 / 500000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-2893924844017 / 500000000000), (-533121371083 / 250000000000), (-310712169953 / 1000000000000), (-266560657189 / 125000000000), (-2893924853219 / 500000000000)], ![(-1299264694561 / 1000000000000), (23130652221 / 62500000000), (370090643517 / 1000000000000), (-649632841753 / 500000000000), (0 / 1)], ![(-928990736017 / 1000000000000), (-928990547817 / 1000000000000), (0 / 1), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 33) : ℤ :=
  ([12, 7, 4, 2, 2, 4, 7, 12] : List ℤ).getD
    ((seed 1 33).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-8016105918843 / 1000000000000), (-4360741903883 / 1000000000000), (-336423173579 / 125000000000), (-217403065613 / 250000000000), (-869612282237 / 1000000000000), (-2691385558001 / 1000000000000), (-545092562491 / 125000000000), (-8016105137269 / 1000000000000)] : List ℚ).getD
    ((seed 1 33).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 33) : ℚ :=
  ([(-4008052959421 / 500000000000), (-2180370951941 / 500000000000), (-2691385388631 / 1000000000000), (-869612262451 / 1000000000000), (-217403070559 / 250000000000), (-1345692779 / 500000000), (-4360740499927 / 1000000000000), (-2004026284317 / 250000000000)] : List ℚ).getD
    ((seed 1 33).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 33) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 33 =>
        (splitWeight 1 33 3 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 33, ∏ i, weights i (c.val i) ≤ 1 := by
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
