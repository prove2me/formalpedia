-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.rational_reciprocal_sum_cubic_rate_gives_positive_eventual_cubic
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:33:43.038139+00:00
-- url     : https://prove2.me/submissions/ddf86405-26ec-4d12-8b04-ad1c4952c548

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubic_over_denominator_tendsto_zero
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_literal_ratio_error_gives_positive_rational_eventual_cubic
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_canonical_integer_tail
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_canonical_tail_ratio_quantitative
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Erdős 243: the rational reciprocal-tail cubic-rate bridge

This file returns from the paper's original sequence `a` to its canonical
positive integer tail numerator.  The quantitative tail comparison makes the
difference between the two consecutive ratios exponentially negligible, so
the literal `n^3`-scaled rate transfers without an extra hypothesis.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter
open ErdosProblems.Erdos243.PaperCompleteR7

theorem cubic_rate_gives_quadratic_growth
    (a : ℕ → ℕ)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ 3)⁻¹) atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa [inv_pow] using hbase.pow 3
  have herr : Tendsto (fun n : ℕ =>
      (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ)))
      atTop (nhds 0) := by
    have hprod := hrate.mul hinv
    simp only [mul_zero] at hprod
    apply hprod.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    field_simp [hn.ne']
  have hinvN : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hmodel : Tendsto (fun n : ℕ => 1 + 3 / (n : ℝ))
      atTop (nhds 1) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := (1 : ℝ))).add
        ((tendsto_const_nhds (x := (3 : ℝ))).mul hinvN)
  have hq : Tendsto (fun n : ℕ => (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))
      atTop (nhds 1) := by
    convert herr.add hmodel using 1 <;> ring
  simpa only [inv_div, inv_one] using hq.inv₀ (by norm_num : (1 : ℝ) ≠ 0)



theorem canonical_numerator_cubic_ratio_error
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n : ℕ => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError
      (fun j => (canonicalNaturalNumerator a p q j : ℝ)) n)
      atTop (nhds 0) := by
  let C := canonicalNaturalNumerator a p q
  have hgrowth := cubic_rate_gives_quadratic_growth a hrate
  obtain ⟨N, hN⟩ :=
    (canonical_tail_ratio_quantitative a ha hpos p q hq hs hgrowth).1
  have hpoly := cubic_over_denominator_tendsto_zero a ha hpos hgrowth
  have hupper : Tendsto (fun n : ℕ =>
      16 * ((n : ℝ) ^ 3 / (a n : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hpoly.const_mul 16
  have htail : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((C (n + 1) : ℝ) / (C n : ℝ) -
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero'
      (g := fun n : ℕ => 16 * ((n : ℝ) ^ 3 / (a n : ℝ)))
    · filter_upwards [] with n
      exact abs_nonneg _
    · filter_upwards [eventually_ge_atTop N] with n hn
      simp only [Function.comp_apply]
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 3)]
      have hh := mul_le_mul_of_nonneg_left (hN n hn) (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 3)
      calc
        (n : ℝ) ^ 3 *
            |(C (n + 1) : ℝ) / (C n : ℝ) -
              (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)|
            ≤ (n : ℝ) ^ 3 * (16 / (a n : ℝ)) := hh
        _ = 16 * ((n : ℝ) ^ 3 / (a n : ℝ)) := by ring
    · exact hupper
  have hsum := htail.add hrate
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [] with n
  simp only [cubicRatioError, C]
  ring
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter
open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n : ℕ => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      atTop (nhds 0)) :
    ∃ A D : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (canonicalNaturalNumerator a p q n : ℝ) =
        (A : ℝ) * risingCubic n + (D : ℝ) := by
  have hCpos := (canonical_integer_tail a hpos p q hq hs).1
  simpa only [Int.cast_natCast] using
    (literal_ratio_error_gives_positive_rational_eventual_cubic
      (fun n => (canonicalNaturalNumerator a p q n : ℤ))
      (fun n => by dsimp only; exact_mod_cast hCpos n)
      (by simpa only [Int.cast_natCast] using
        canonical_numerator_cubic_ratio_error a ha hpos p q hq hs hrate))
