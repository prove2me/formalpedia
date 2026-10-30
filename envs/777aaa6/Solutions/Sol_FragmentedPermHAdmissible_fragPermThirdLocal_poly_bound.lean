-- Prove2me | solution 1 for FragmentedPermHAdmissible.fragPermThirdLocal_poly_bound
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T17:00:08.864105+00:00
-- url     : https://prove2.me/submissions/a4c0b3fb-76b2-4438-9f97-100c8ba49c35

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_FragmentedPermThirdOrder
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Third-order saddle data for fragmented permutations

This file adds the finite-radius third-order correction layer for
`exp (z / (1 - z))`.  The proof uses the narrower finite-radius window
`(1-r)^(29/20)`, because the second-order window is too wide for an
`o((1-r)^2)` third-order remainder.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

noncomputable section

namespace FragmentedPermHAdmissible

private lemma fragPermThirdScaledRemainderConst_pos :
    0 < fragPermThirdScaledRemainderConst := by
  unfold fragPermThirdScaledRemainderConst
  positivity

end FragmentedPermHAdmissible
end

open FragmentedPermHAdmissible
open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
theorem solution {y : ℝ} (hy0 : 0 ≤ y) :
    let K : ℝ := fragPermThirdScaledRemainderConst
    let S1 : ℝ := 10 * y ^ 3 + 10 * y ^ 4 + 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
    let S2 : ℝ := 10 * y ^ 4 + 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
    let S3 : ℝ := 10 * y ^ 6 + K * y ^ 7
    let S4 : ℝ := 40 * y ^ 5 + 10 * y ^ 6 + K * y ^ 7
    let G : ℝ := ∑ k ∈ Finset.range 36, y ^ k
    Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
      (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
      (3 * (10 * y ^ 3) ^ 2 * S4 + 3 * (10 * y ^ 3) * S2 ^ 2 + S2 ^ 3) +
      S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
        S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
        ≤ fragPermThirdLocalL1Const * G := by
  intro K S1 S2 S3 S4 G
  let B0 : ℝ := y ^ 3 + y ^ 4 + y ^ 5 + y ^ 6 + y ^ 7
  let L : ℝ := 100 + K
  have hK : 0 ≤ K := by
    dsimp [K]
    exact fragPermThirdScaledRemainderConst_pos.le
  have hE1 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hB0_nonneg : 0 ≤ B0 := by dsimp [B0]; positivity
  have hL_nonneg : 0 ≤ L := by dsimp [L]; positivity
  have hL_ge_one : 1 ≤ L := by dsimp [L]; nlinarith [hK]
  have hLsum_nonneg :
      0 ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by positivity
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact Finset.sum_nonneg fun k hk => pow_nonneg hy0 k
  have hpow_le_G : ∀ {m : ℕ}, m < 36 → y ^ m ≤ G := by
    intro m hm
    dsimp [G]
    exact Finset.single_le_sum (fun k hk => pow_nonneg hy0 k)
      (Finset.mem_range.mpr hm)
  have hG_ge_one : 1 ≤ G := by
    simpa using (hpow_le_G (m := 0) (by norm_num))
  have hB0_le_five_of_le_one (hy1 : y ≤ 1) : B0 ≤ 5 := by
    dsimp [B0]
    have h3 : y ^ 3 ≤ 1 := by simpa using (pow_le_one₀ (n := 3) hy0 hy1)
    have h4 : y ^ 4 ≤ 1 := by simpa using (pow_le_one₀ (n := 4) hy0 hy1)
    have h5 : y ^ 5 ≤ 1 := by simpa using (pow_le_one₀ (n := 5) hy0 hy1)
    have h6 : y ^ 6 ≤ 1 := by simpa using (pow_le_one₀ (n := 6) hy0 hy1)
    have h7 : y ^ 7 ≤ 1 := by simpa using (pow_le_one₀ (n := 7) hy0 hy1)
    nlinarith
  have hB0_le_five_y7_of_ge_one (hy1 : 1 ≤ y) : B0 ≤ 5 * y ^ 7 := by
    dsimp [B0]
    have h3 : y ^ 3 ≤ y ^ 7 := pow_le_pow_right₀ hy1 (by norm_num)
    have h4 : y ^ 4 ≤ y ^ 7 := pow_le_pow_right₀ hy1 (by norm_num)
    have h5 : y ^ 5 ≤ y ^ 7 := pow_le_pow_right₀ hy1 (by norm_num)
    have h6 : y ^ 6 ≤ y ^ 7 := pow_le_pow_right₀ hy1 (by norm_num)
    nlinarith
  have hB1 : B0 ≤ 5 * G := by
    by_cases hy1 : y ≤ 1
    · calc
        B0 ≤ 5 := hB0_le_five_of_le_one hy1
        _ ≤ 5 * G := by nlinarith [hG_ge_one]
    · have hyge : 1 ≤ y := by linarith
      calc
        B0 ≤ 5 * y ^ 7 := hB0_le_five_y7_of_ge_one hyge
        _ ≤ 5 * G := by
          exact mul_le_mul_of_nonneg_left
            (hpow_le_G (m := 7) (by norm_num)) (by norm_num)
  have hB2 : B0 ^ 2 ≤ 25 * G := by
    by_cases hy1 : y ≤ 1
    · calc
        B0 ^ 2 ≤ 5 ^ 2 := pow_le_pow_left₀ hB0_nonneg (hB0_le_five_of_le_one hy1) 2
        _ = (25 : ℝ) := by norm_num
        _ ≤ 25 * G := by nlinarith [hG_ge_one]
    · have hyge : 1 ≤ y := by linarith
      calc
        B0 ^ 2 ≤ (5 * y ^ 7) ^ 2 :=
          pow_le_pow_left₀ hB0_nonneg (hB0_le_five_y7_of_ge_one hyge) 2
        _ = 25 * y ^ 14 := by ring
        _ ≤ 25 * G :=
          mul_le_mul_of_nonneg_left (hpow_le_G (m := 14) (by norm_num))
            (by norm_num)
  have hB3 : B0 ^ 3 ≤ 125 * G := by
    by_cases hy1 : y ≤ 1
    · calc
        B0 ^ 3 ≤ 5 ^ 3 := pow_le_pow_left₀ hB0_nonneg (hB0_le_five_of_le_one hy1) 3
        _ = (125 : ℝ) := by norm_num
        _ ≤ 125 * G := by nlinarith [hG_ge_one]
    · have hyge : 1 ≤ y := by linarith
      calc
        B0 ^ 3 ≤ (5 * y ^ 7) ^ 3 :=
          pow_le_pow_left₀ hB0_nonneg (hB0_le_five_y7_of_ge_one hyge) 3
        _ = 125 * y ^ 21 := by ring
        _ ≤ 125 * G :=
          mul_le_mul_of_nonneg_left (hpow_le_G (m := 21) (by norm_num))
            (by norm_num)
  have hB4 : B0 ^ 4 ≤ 625 * G := by
    by_cases hy1 : y ≤ 1
    · calc
        B0 ^ 4 ≤ 5 ^ 4 := pow_le_pow_left₀ hB0_nonneg (hB0_le_five_of_le_one hy1) 4
        _ = (625 : ℝ) := by norm_num
        _ ≤ 625 * G := by nlinarith [hG_ge_one]
    · have hyge : 1 ≤ y := by linarith
      calc
        B0 ^ 4 ≤ (5 * y ^ 7) ^ 4 :=
          pow_le_pow_left₀ hB0_nonneg (hB0_le_five_y7_of_ge_one hyge) 4
        _ = 625 * y ^ 28 := by ring
        _ ≤ 625 * G :=
          mul_le_mul_of_nonneg_left (hpow_le_G (m := 28) (by norm_num))
            (by norm_num)
  have hB5 : B0 ^ 5 ≤ 3125 * G := by
    by_cases hy1 : y ≤ 1
    · calc
        B0 ^ 5 ≤ 5 ^ 5 := pow_le_pow_left₀ hB0_nonneg (hB0_le_five_of_le_one hy1) 5
        _ = (3125 : ℝ) := by norm_num
        _ ≤ 3125 * G := by nlinarith [hG_ge_one]
    · have hyge : 1 ≤ y := by linarith
      calc
        B0 ^ 5 ≤ (5 * y ^ 7) ^ 5 :=
          pow_le_pow_left₀ hB0_nonneg (hB0_le_five_y7_of_ge_one hyge) 5
        _ = 3125 * y ^ 35 := by ring
        _ ≤ 3125 * G :=
          mul_le_mul_of_nonneg_left (hpow_le_G (m := 35) (by norm_num))
            (by norm_num)
  have hLsum_ge1 : 1 ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by
    nlinarith [pow_nonneg hL_nonneg 2, pow_nonneg hL_nonneg 3,
      pow_nonneg hL_nonneg 4, pow_nonneg hL_nonneg 5, hL_nonneg]
  have hLpow2 : L ^ 2 ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by
    nlinarith [pow_nonneg hL_nonneg 3, pow_nonneg hL_nonneg 4,
      pow_nonneg hL_nonneg 5, hL_nonneg]
  have hLpow3 : L ^ 3 ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by
    nlinarith [pow_nonneg hL_nonneg 2, pow_nonneg hL_nonneg 4,
      pow_nonneg hL_nonneg 5, hL_nonneg]
  have hLpow4 : L ^ 4 ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by
    nlinarith [pow_nonneg hL_nonneg 2, pow_nonneg hL_nonneg 3,
      pow_nonneg hL_nonneg 5, hL_nonneg]
  have hLpow5 : L ^ 5 ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by
    nlinarith [pow_nonneg hL_nonneg 2, pow_nonneg hL_nonneg 3,
      pow_nonneg hL_nonneg 4, hL_nonneg]
  have hS1 : S1 ≤ L * B0 := by
    dsimp [S1, L, B0]
    nlinarith [hK, pow_nonneg hy0 3, pow_nonneg hy0 4, pow_nonneg hy0 5,
      pow_nonneg hy0 6, pow_nonneg hy0 7]
  have hS2 : S2 ≤ L * B0 := by
    dsimp [S2, L, B0]
    nlinarith [hK, pow_nonneg hy0 3, pow_nonneg hy0 4, pow_nonneg hy0 5,
      pow_nonneg hy0 6, pow_nonneg hy0 7]
  have hS3 : S3 ≤ L * B0 := by
    dsimp [S3, L, B0]
    nlinarith [hK, pow_nonneg hy0 3, pow_nonneg hy0 4, pow_nonneg hy0 5,
      pow_nonneg hy0 6, pow_nonneg hy0 7]
  have hS4 : S4 ≤ L * B0 := by
    dsimp [S4, L, B0]
    nlinarith [hK, pow_nonneg hy0 3, pow_nonneg hy0 4, pow_nonneg hy0 5,
      pow_nonneg hy0 6, pow_nonneg hy0 7]
  have hT : 10 * y ^ 3 ≤ L * B0 := by
    dsimp [L, B0]
    nlinarith [hK, pow_nonneg hy0 3, pow_nonneg hy0 4, pow_nonneg hy0 5,
      pow_nonneg hy0 6, pow_nonneg hy0 7]
  have hK_le_Lsum : K ≤ L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1 := by
    dsimp [L]
    nlinarith [hK, pow_nonneg hL_nonneg 2, pow_nonneg hL_nonneg 3,
      pow_nonneg hL_nonneg 4, pow_nonneg hL_nonneg 5]
  have hS1_nonneg : 0 ≤ S1 := by dsimp [S1]; positivity
  have hS2_nonneg : 0 ≤ S2 := by dsimp [S2]; positivity
  have hS3_nonneg : 0 ≤ S3 := by dsimp [S3]; positivity
  have hS4_nonneg : 0 ≤ S4 := by dsimp [S4]; positivity
  have hT_nonneg : 0 ≤ 10 * y ^ 3 := by positivity
  have hLsumG_nonneg :
      0 ≤ (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G :=
    mul_nonneg hLsum_nonneg hG_nonneg
  have hy7_le_G : y ^ 7 ≤ G := by
    exact hpow_le_G (m := 7) (by norm_num)
  have hy9_le_G : y ^ 9 ≤ G := by
    exact hpow_le_G (m := 9) (by norm_num)
  have hy10_le_G : y ^ 10 ≤ G := by
    exact hpow_le_G (m := 10) (by norm_num)
  have hG_le_LsumG :
      G ≤ (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G := by
    calc
      G = 1 * G := by ring
      _ ≤ (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G :=
        mul_le_mul_of_nonneg_right hLsum_ge1 hG_nonneg
  have hS1_5 : S1 ^ 5 ≤ L ^ 5 * B0 ^ 5 := by
    calc
      S1 ^ 5 ≤ (L * B0) ^ 5 := pow_le_pow_left₀ hS1_nonneg hS1 5
      _ = L ^ 5 * B0 ^ 5 := by ring
  have hS1S3 : S1 * S3 ≤ L ^ 2 * B0 ^ 2 := by
    calc
      S1 * S3 ≤ (L * B0) * (L * B0) :=
        mul_le_mul hS1 hS3 hS3_nonneg (mul_nonneg hL_nonneg hB0_nonneg)
      _ = L ^ 2 * B0 ^ 2 := by ring
  have hS3sq : S3 ^ 2 ≤ L ^ 2 * B0 ^ 2 := by
    calc
      S3 ^ 2 ≤ (L * B0) ^ 2 := pow_le_pow_left₀ hS3_nonneg hS3 2
      _ = L ^ 2 * B0 ^ 2 := by ring
  have hT2S4 : (10 * y ^ 3) ^ 2 * S4 ≤ L ^ 3 * B0 ^ 3 := by
    have hT2 : (10 * y ^ 3) ^ 2 ≤ (L * B0) ^ 2 :=
      pow_le_pow_left₀ hT_nonneg hT 2
    calc
      (10 * y ^ 3) ^ 2 * S4 ≤ (L * B0) ^ 2 * (L * B0) :=
        mul_le_mul hT2 hS4 hS4_nonneg (pow_nonneg (mul_nonneg hL_nonneg hB0_nonneg) 2)
      _ = L ^ 3 * B0 ^ 3 := by ring
  have hTS2sq : (10 * y ^ 3) * S2 ^ 2 ≤ L ^ 3 * B0 ^ 3 := by
    have hS2sq : S2 ^ 2 ≤ (L * B0) ^ 2 :=
      pow_le_pow_left₀ hS2_nonneg hS2 2
    calc
      (10 * y ^ 3) * S2 ^ 2 ≤ (L * B0) * (L * B0) ^ 2 :=
        mul_le_mul hT hS2sq (pow_nonneg hS2_nonneg 2) (mul_nonneg hL_nonneg hB0_nonneg)
      _ = L ^ 3 * B0 ^ 3 := by ring
  have hS2_3 : S2 ^ 3 ≤ L ^ 3 * B0 ^ 3 := by
    calc
      S2 ^ 3 ≤ (L * B0) ^ 3 := pow_le_pow_left₀ hS2_nonneg hS2 3
      _ = L ^ 3 * B0 ^ 3 := by ring
  have hfour_poly :
      S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
        S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
        ≤ 4 * L ^ 4 * B0 ^ 4 := by
    have hS1_3 : S1 ^ 3 ≤ (L * B0) ^ 3 :=
      pow_le_pow_left₀ hS1_nonneg hS1 3
    have hS1_2T : S1 ^ 2 * (10 * y ^ 3) ≤ (L * B0) ^ 3 := by
      have hS1_2 : S1 ^ 2 ≤ (L * B0) ^ 2 :=
        pow_le_pow_left₀ hS1_nonneg hS1 2
      calc
        S1 ^ 2 * (10 * y ^ 3) ≤ (L * B0) ^ 2 * (L * B0) :=
          mul_le_mul hS1_2 hT hT_nonneg (pow_nonneg (mul_nonneg hL_nonneg hB0_nonneg) 2)
        _ = (L * B0) ^ 3 := by ring
    have hS1T2 : S1 * (10 * y ^ 3) ^ 2 ≤ (L * B0) ^ 3 := by
      have hT2 : (10 * y ^ 3) ^ 2 ≤ (L * B0) ^ 2 :=
        pow_le_pow_left₀ hT_nonneg hT 2
      calc
        S1 * (10 * y ^ 3) ^ 2 ≤ (L * B0) * (L * B0) ^ 2 :=
          mul_le_mul hS1 hT2 (pow_nonneg hT_nonneg 2) (mul_nonneg hL_nonneg hB0_nonneg)
        _ = (L * B0) ^ 3 := by ring
    have hT3 : (10 * y ^ 3) ^ 3 ≤ (L * B0) ^ 3 :=
      pow_le_pow_left₀ hT_nonneg hT 3
    have hsum4 :
        S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
          S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3
          ≤ 4 * (L * B0) ^ 3 := by
      linarith [hS1_3, hS1_2T, hS1T2, hT3]
    calc
      S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
        S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
          ≤ (L * B0) * (4 * (L * B0) ^ 3) := by
            exact mul_le_mul hS2 hsum4
              (by positivity) (mul_nonneg hL_nonneg hB0_nonneg)
      _ = 4 * L ^ 4 * B0 ^ 4 := by ring
  have hL2B2 :
      L ^ 2 * B0 ^ 2 ≤
        25 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
    calc
      L ^ 2 * B0 ^ 2 ≤
          (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * (25 * G) :=
        mul_le_mul hLpow2 hB2 (pow_nonneg hB0_nonneg 2) hLsum_nonneg
      _ = 25 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
  have hL3B3 :
      L ^ 3 * B0 ^ 3 ≤
        125 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
    calc
      L ^ 3 * B0 ^ 3 ≤
          (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * (125 * G) :=
        mul_le_mul hLpow3 hB3 (pow_nonneg hB0_nonneg 3) hLsum_nonneg
      _ = 125 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
  have hL4B4 :
      L ^ 4 * B0 ^ 4 ≤
        625 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
    calc
      L ^ 4 * B0 ^ 4 ≤
          (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * (625 * G) :=
        mul_le_mul hLpow4 hB4 (pow_nonneg hB0_nonneg 4) hLsum_nonneg
      _ = 625 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
  have hL5B5 :
      L ^ 5 * B0 ^ 5 ≤
        3125 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
    calc
      L ^ 5 * B0 ^ 5 ≤
          (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * (3125 * G) :=
        mul_le_mul hLpow5 hB5 (pow_nonneg hB0_nonneg 5) hLsum_nonneg
      _ = 3125 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
  have hpoly_to :
      Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
      (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
      (3 * (10 * y ^ 3) ^ 2 * S4 + 3 * (10 * y ^ 3) * S2 ^ 2 + S2 ^ 3) +
      S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
        S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
        ≤
      10000 * (Real.exp 1 + 1) *
        (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G := by
    have hExp :
        Real.exp 1 * S1 ^ 5 ≤
          3125 * Real.exp 1 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
      calc
        Real.exp 1 * S1 ^ 5 ≤ Real.exp 1 * (L ^ 5 * B0 ^ 5) :=
          mul_le_mul_of_nonneg_left hS1_5 hE1
        _ ≤ Real.exp 1 *
              (3125 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G)) :=
          mul_le_mul_of_nonneg_left hL5B5 hE1
        _ = 3125 * Real.exp 1 *
              ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
    have hR :
        K * y ^ 7 ≤
          (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G := by
      exact mul_le_mul hK_le_Lsum hy7_le_G (pow_nonneg hy0 7) hLsum_nonneg
    have hQuad :
        1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2 ≤
          2475 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
      have hy10_L :
          y ^ 10 ≤ (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G :=
        hy10_le_G.trans hG_le_LsumG
      have hy9_L :
          y ^ 9 ≤ (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G :=
        hy9_le_G.trans hG_le_LsumG
      have hS1S3_L :
          S1 * S3 ≤ 25 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) :=
        hS1S3.trans hL2B2
      have hS3sq_L :
          S3 ^ 2 ≤ 25 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) :=
        hS3sq.trans hL2B2
      linarith
    have hCube :
        3 * (10 * y ^ 3) ^ 2 * S4 + 3 * (10 * y ^ 3) * S2 ^ 2 + S2 ^ 3 ≤
          875 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
      have hT2S4_L :
          (10 * y ^ 3) ^ 2 * S4 ≤ 125 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) :=
        hT2S4.trans hL3B3
      have hTS2sq_L :
          (10 * y ^ 3) * S2 ^ 2 ≤ 125 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) :=
        hTS2sq.trans hL3B3
      have hS2_3_L :
          S2 ^ 3 ≤ 125 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) :=
        hS2_3.trans hL3B3
      linarith
    have hFourth :
        S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
          S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3) ≤
          2500 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
      calc
        S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
            S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
            ≤ 4 * L ^ 4 * B0 ^ 4 := hfour_poly
        _ = 4 * (L ^ 4 * B0 ^ 4) := by ring
        _ ≤ 4 *
            (625 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G)) :=
          mul_le_mul_of_nonneg_left hL4B4 (by norm_num : (0 : ℝ) ≤ 4)
        _ = 2500 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
    have hcoef :
        3125 * Real.exp 1 + 5851 ≤ 10000 * (Real.exp 1 + 1) := by
      linarith [hE1]
    calc
      Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
        (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
        (3 * (10 * y ^ 3) ^ 2 * S4 + 3 * (10 * y ^ 3) * S2 ^ 2 + S2 ^ 3) +
        S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
          S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
          ≤
        3125 * Real.exp 1 *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) +
          (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G +
          2475 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) +
          875 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) +
          2500 * ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
            linarith
      _ = (3125 * Real.exp 1 + 5851) *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
      _ ≤ (10000 * (Real.exp 1 + 1)) *
            ((L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by
        exact mul_le_mul_of_nonneg_right hcoef hLsumG_nonneg
      _ = 10000 * (Real.exp 1 + 1) *
            (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G := by
        rw [← mul_assoc]
  calc
    Real.exp 1 * S1 ^ 5 + K * y ^ 7 +
      (1600 * y ^ 10 + 800 * y ^ 9 + 2 * S1 * S3 + S3 ^ 2) +
      (3 * (10 * y ^ 3) ^ 2 * S4 + 3 * (10 * y ^ 3) * S2 ^ 2 + S2 ^ 3) +
      S2 * (S1 ^ 3 + S1 ^ 2 * (10 * y ^ 3) +
        S1 * (10 * y ^ 3) ^ 2 + (10 * y ^ 3) ^ 3)
        ≤ 10000 * (Real.exp 1 + 1) *
        (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G := hpoly_to
    _ ≤ fragPermThirdLocalL1Const * G := by
      have hbase_nonneg :
          0 ≤ (Real.exp 1 + 1) *
              (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G := by
        exact mul_nonneg (mul_nonneg (by positivity) hLsum_nonneg) hG_nonneg
      calc
        10000 * (Real.exp 1 + 1) *
            (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G
            = 10000 * ((Real.exp 1 + 1) *
                (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) := by ring
        _ ≤ 100000 * ((Real.exp 1 + 1) *
              (L ^ 5 + L ^ 4 + L ^ 3 + L ^ 2 + L + 1) * G) :=
          mul_le_mul_of_nonneg_right (by norm_num : (10000 : ℝ) ≤ 100000)
            hbase_nonneg
        _ = fragPermThirdLocalL1Const * G := by
          dsimp [fragPermThirdLocalL1Const, L, K]
          ring
