-- Prove2me | solution 1 for mme_released_interior_owner2_cell19_region0_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:37:02.268249+00:00
-- url     : https://prove2.me/submissions/c4f17135-ad82-4b56-a23b-2c74c3c1ff1f

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 2 19 0 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(102559824249 / 250000000000), (398647603857 / 500000000000), (205122601233 / 500000000000), (1 / 1), (1 / 1)], ![(1703112925250000000000000000000000 / 84423733945031272621271145739719963), (10032905702575000000000000000000000 / 253271201835093817863813437219159889), (5109412349075000000000000000000000 / 253271201835093817863813437219159889), (1 / 1), (1 / 1)], ![(38722386091 / 1000000000000), (1128446547813 / 500000000000), (17729166083841 / 1000000000000), (2256925881489 / 1000000000000), (9680605531 / 250000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![6, 5, 6, 0, 0], ![5, -1, -4, -1, 5]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-891014638333 / 1000000000000), (-28316283767 / 125000000000), (-891000243253 / 1000000000000), (0 / 1), (0 / 1)], ![(-975847715217 / 250000000000), (-1614295298723 / 500000000000), (-3903376461197 / 1000000000000), (0 / 1), (0 / 1)], ![(-1625668697111 / 500000000000), (406994565509 / 500000000000), (2875211084791 / 1000000000000), (407001828951 / 500000000000), (-130053458547 / 40000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-222753659583 / 250000000000), (-45306054027 / 200000000000), (-222750060813 / 250000000000), (0 / 1), (0 / 1)], ![(-3903390860867 / 1000000000000), (-645718119489 / 200000000000), (-975844115299 / 250000000000), (0 / 1), (0 / 1)], ![(-3251337394221 / 1000000000000), (813989131019 / 1000000000000), (359401385599 / 125000000000), (814003657903 / 1000000000000), (-1625668231837 / 500000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 19) : ℤ :=
  ([12, 5, 3, 5, 1, 5, 3, 5, 12] : List ℤ).getD
    ((seed 2 19).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-8045741963573 / 1000000000000), (-663183494613 / 200000000000), (-239897502417 / 125000000000), (-1652800788949 / 500000000000), (-57990978279 / 100000000000), (-330560170967 / 100000000000), (-1919180014729 / 1000000000000), (-663183520067 / 200000000000), (-8045714098079 / 1000000000000)] : List ℚ).getD
    ((seed 2 19).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 19) : ℚ :=
  ([(-2011435490893 / 250000000000), (-414489684133 / 125000000000), (-383836003867 / 200000000000), (-3305601577897 / 1000000000000), (-579909782789 / 1000000000000), (-3305601709669 / 1000000000000), (-239897501841 / 125000000000), (-1657958800167 / 500000000000), (-4022857049039 / 500000000000)] : List ℚ).getD
    ((seed 2 19).splits.idxOf (sourceShape 2 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_pos : ∀ c, 0 < alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 19) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) (alpha_pos c)
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c; decide +kernel

/-- A rational product dual bounds the natural-log entropy penalty of the
actual released interior split distribution. -/
theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 19 =>
        (splitWeight 2 19 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 19, ∏ i, weights i (c.val i) ≤ 1 := by
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
