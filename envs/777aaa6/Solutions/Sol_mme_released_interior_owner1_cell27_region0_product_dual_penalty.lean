-- Prove2me | solution 1 for mme_released_interior_owner1_cell27_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T14:55:32.053269+00:00
-- url     : https://prove2.me/submissions/4380626e-23cb-4ff4-9053-1ca6dafa66c3

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 1 27 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(169730267383000000000000000000000000 / 15857597799394983802701771548265522519), (813597838846000000000000000000000000 / 5285865933131661267567257182755174173), (813553994357000000000000000000000000 / 5285865933131661267567257182755174173), (169702475500000000000000000000000000 / 15857597799394983802701771548265522519), (1 / 1)], ![(175633510589 / 1000000000000), (2355799674083 / 1000000000000), (471134501451 / 200000000000), (87802617647 / 500000000000), (1 / 1)], ![(445262425389 / 1000000000000), (54069742609 / 62500000000), (445214378577 / 1000000000000), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![7, 3, 3, 7, 0], ![3, -1, -1, 3, 0], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-907438701273 / 200000000000), (-1871325543767 / 1000000000000), (-467844858713 / 250000000000), (-4537357261239 / 1000000000000), (0 / 1)], ![(-1739355781199 / 1000000000000), (171376046839 / 200000000000), (171365250483 / 200000000000), (-1739516784479 / 1000000000000), (0 / 1)], ![(-404545725329 / 500000000000), (-144891813689 / 1000000000000), (-809199363209 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1134298376591 / 250000000000), (-935662771883 / 500000000000), (-1871379434851 / 1000000000000), (-2268678630619 / 500000000000), (0 / 1)], ![(-869677890599 / 500000000000), (214220058549 / 250000000000), (6693955097 / 7812500000), (-869758392239 / 500000000000), (0 / 1)], ![(-809091450657 / 1000000000000), (-18111476711 / 125000000000), (-101149920401 / 125000000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 27) : ℤ :=
  ([10, 7, 7, 2, 3, 3, 2, 7, 7, 10] : List ℤ).getD
    ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-3203769328699 / 500000000000), (-561452531203 / 125000000000), (-442184914393 / 100000000000), (-1159464525061 / 1000000000000), (-227919925931 / 125000000000), (-911679683889 / 500000000000), (-289866108651 / 250000000000), (-884369987877 / 200000000000), (-70181595423 / 15625000000), (-51260331337 / 8000000000)] : List ℚ).getD
    ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 27) : ℚ :=
  ([(-6407538657397 / 1000000000000), (-4491620249623 / 1000000000000), (-4421849143929 / 1000000000000), (-57973226253 / 50000000000), (-1823359407447 / 1000000000000), (-1823359367777 / 1000000000000), (-1159464434603 / 1000000000000), (-552731242423 / 125000000000), (-4491622107071 / 1000000000000), (-1601885354281 / 250000000000)] : List ℚ).getD
    ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 27) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 1 27 0 c : ℝ) / 1000000000000) ≤
          (431 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 27, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    (fun c => (alpha_pos c).le) hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c _ => (alpha_logs c).2)
    (431 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((431 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound


#print axioms solution
