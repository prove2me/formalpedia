-- Prove2me | solution 1 for mme_released_interior_owner3_cell25_region2_product_dual_penalty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:14:31.137448+00:00
-- url     : https://prove2.me/submissions/0f6b6b67-ee1e-4ee4-ba82-0890762eaf14

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 3 25 2 c : ℚ) / 1000000000000

private def weights : Fin 3 → Fin 5 → ℚ :=
  ![![(9901961546981800980384530181 / 50000000000000000000000000000), (3793305485979662066945140203 / 4000000000000000000000000000), (2963519982518270364800174817 / 3125000000000000000000000000), (19803884206272501961157937273 / 100000000000000000000000000000), (1 / 1)], ![(10000000159543999999998404559 / 20000000000000000000000000000), (9999999840455800000001595441 / 20000000000000000000000000000), (1 / 1), (1 / 1), (1 / 1)], ![(331461266706896685387332931 / 100000000000000000000000000000), (2464223621644275357763783557 / 20000000000000000000000000000), (9048557291323209514427086767 / 10000000000000000000000000000), (12321115491876976788845081229 / 100000000000000000000000000000), (331455525459696685444745403 / 100000000000000000000000000000)]]

private def weightScale : Fin 3 → Fin 5 → ℤ :=
  ![![2, 0, 0, 2, 0], ![1, 1, 0, 0, 0], ![8, 3, 0, 3, 8]]

private def weightLower : Fin 3 → Fin 5 → ℚ :=
  ![![(-202411266481899 / 125000000000000), (-6632070280863 / 125000000000000), (-53056538087573 / 1000000000000000), (-202411511936607 / 125000000000000), (0 / 1)], ![(-346573582302773 / 500000000000000), (-346573598257183 / 500000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-1141882900936813 / 200000000000000), (-418771095292661 / 200000000000000), (-99979763313587 / 1000000000000000), (-261731961101209 / 125000000000000), (-2854715912926993 / 500000000000000)]]

private def weightUpper : Fin 3 → Fin 5 → ℚ :=
  ![![(-1619290131855189 / 1000000000000000), (-53056562246903 / 1000000000000000), (-13264134521893 / 250000000000000), (-1619292095492853 / 1000000000000000), (0 / 1)], ![(-138629432921109 / 200000000000000), (-138629439302873 / 200000000000000), (0 / 1), (0 / 1), (0 / 1)], ![(-2854707252342029 / 500000000000000), (-2093855476463301 / 1000000000000000), (-49989881656793 / 500000000000000), (-2093855688809669 / 1000000000000000), (-2854715912926989 / 500000000000000)]]

private def alphaScale (c : MME.ReleasedInterior.Split 25) : ℤ :=
  ([12, 4, 6, 1, 1, 6, 4, 12] : List ℤ).getD
    ((seed 3 25).splits.idxOf (sourceShape 3 c)) 0

private def alphaLower (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-2005463449172801 / 250000000000000), (-568011842213043 / 200000000000000), (-1101573684140419 / 250000000000000), (-211545880518707 / 250000000000000), (-211545866501669 / 250000000000000), (-2203146508589603 / 500000000000000), (-177503713478881 / 62500000000000), (-8021869122314681 / 1000000000000000)] : List ℚ).getD
    ((seed 3 25).splits.idxOf (sourceShape 3 c)) 0

private def alphaUpper (c : MME.ReleasedInterior.Split 25) : ℚ :=
  ([(-8021853796691193 / 1000000000000000), (-2840059211065211 / 1000000000000000), (-440629473656167 / 100000000000000), (-423091761037413 / 500000000000000), (-423091733003337 / 500000000000000), (-2753933135737 / 625000000000), (-2840059415662091 / 1000000000000000), (-802186912231467 / 100000000000000)] : List ℚ).getD
    ((seed 3 25).splits.idxOf (sourceShape 3 c)) 0

private theorem weights_pos : ∀ i j, 0 < weights i j := by decide +kernel

private theorem alpha_nonneg : ∀ c, 0 ≤ alphaQ c := by decide +kernel

private theorem weight_logs (i : Fin 3) (j : Fin 5) :
    (weightLower i j : ℝ) ≤ Real.log (weights i j : ℝ) ∧
      Real.log (weights i j : ℝ) ≤ (weightUpper i j : ℝ) := by
  apply mme_rational_log_series_certificate (weights i j) (weights_pos i j)
    (weightScale i j) 16 (weightLower i j) (weightUpper i j)
  all_goals revert i j; decide +kernel

private theorem alpha_logs (c : MME.ReleasedInterior.Split 25) (hc : 0 < alphaQ c) :
    (alphaLower c : ℝ) ≤ Real.log (alphaQ c : ℝ) ∧
      Real.log (alphaQ c : ℝ) ≤ (alphaUpper c : ℝ) := by
  apply mme_rational_log_series_certificate (alphaQ c) hc
    (alphaScale c) 16 (alphaLower c) (alphaUpper c)
  all_goals revert c hc; decide +kernel

theorem solution :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 25 =>
        (splitWeight 3 25 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  have hmass : ∑ c : MME.ReleasedInterior.Split 25, ∏ i, weights i (c.val i) ≤ 1 := by
    decide +kernel
  have h := mme_rational_product_dual_penalty_certificate alphaQ
    alpha_nonneg hprob weights weights_pos hmass weightLower alphaUpper
    (fun i j => (weight_logs i j).1) (fun c hc => (alpha_logs c hc).2)
    (1 / 1000000000)
  have hbound : Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c => (alphaQ c : ℝ)) ≤ ((1 / 1000000000 : ℚ) : ℝ) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_zero] using hbound
