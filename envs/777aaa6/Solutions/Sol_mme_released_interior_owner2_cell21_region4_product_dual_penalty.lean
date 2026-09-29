-- Prove2me | solution 1 for mme_released_interior_owner2_cell21_region4_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:17.585032+00:00
-- url     : https://prove2.me/submissions/b6b6d956-6abd-4957-88b9-e6f33194e1d3

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 2 21 4 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(418516067787 / 1000000000000), (97095101787 / 125000000000), (16740022877 / 40000000000), (1 / 1), (1 / 1)], ![(9741924691750000000000000000000000 / 4993789675793449514970987536061715021), (573011709071750000000000000000000000 / 4993789675793449514970987536061715021), (4277161184475250000000000000000000000 / 4993789675793449514970987536061715021), (572990309312500000000000000000000000 / 4993789675793449514970987536061715021), (1391702364750000000000000000000000 / 713398525113349930710141076580245003)], ![(402727835181 / 1000000000000), (209777977887 / 250000000000), (19663717 / 48828125), (1 / 1), (1 / 1)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 1, 2, 0, 0], ![10, 4, 1, 4, 10], ![2, 1, 2, 0, 0]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-435519998017 / 500000000000), (-126311404157 / 500000000000), (-871077022447 / 1000000000000), (0 / 1), (0 / 1)], ![(-1247902329897 / 200000000000), (-2165044203387 / 1000000000000), (-154905560717 / 1000000000000), (-541270387549 / 250000000000), (-1247902496979 / 200000000000)], ![(-909494292131 / 1000000000000), (-175411194583 / 1000000000000), (-909531317873 / 1000000000000), (0 / 1), (0 / 1)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-871039996033 / 1000000000000), (-252622808313 / 1000000000000), (-435538511223 / 500000000000), (0 / 1), (0 / 1)], ![(-1559877912371 / 250000000000), (-1082522101693 / 500000000000), (-38726390179 / 250000000000), (-433016310039 / 200000000000), (-3119756242447 / 500000000000)], ![(-90949429213 / 100000000000), (-87705597291 / 500000000000), (-56845707367 / 62500000000), (0 / 1), (0 / 1)]]

private def alphaScale (c : MME.ReleasedInterior.Split 21) : ℤ :=
  ([12, 5, 5, 3, 1, 3, 5, 5, 12] : List ℤ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-8020119990203 / 1000000000000), (-1663599173999 / 500000000000), (-642306480801 / 200000000000), (-483869217511 / 250000000000), (-145734890903 / 250000000000), (-967738439937 / 500000000000), (-3211532757227 / 1000000000000), (-831799658057 / 250000000000), (-2005011693459 / 250000000000)] : List ℚ).getD
    ((seed 2 21).splits.idxOf (sourceShape 2 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 21) : ℚ :=
  ([(-4010059995101 / 500000000000), (-3327198347997 / 1000000000000), (-802883101001 / 250000000000), (-1935476870043 / 1000000000000), (-582939563611 / 1000000000000), (-1935476879873 / 1000000000000), (-1605766378613 / 500000000000), (-3327198632227 / 1000000000000), (-1604009354767 / 200000000000)] : List ℚ).getD
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
        (splitWeight 2 21 4 c : ℝ) / 1000000000000) ≤
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
