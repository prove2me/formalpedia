-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.cubic_over_denominator_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:04:31.297766+00:00
-- url     : https://prove2.me/submissions/08088f80-fa4e-4886-af69-e6f0ce723fff

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_positive_sequence_zero_of_ratio_zero
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_reciprocal_successive_ratio_tendsto_zero
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_shift_tendsto_atTop
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
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter
open ErdosProblems.Erdos243.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 3 / (a n : ℝ)) atTop (nhds 0) := by
  let u : ℕ → ℝ := fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 3 / (a n : ℝ)
  have hu : ∀ n, 0 < u n := by
    intro n
    exact div_pos (by positivity) (by exact_mod_cast hpos n)
  have hnlarge : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (shift_tendsto_atTop 1)
  have hninv := tendsto_inv_atTop_zero.comp hnlarge
  have hlinear : Tendsto
      (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
    have hh : Tendsto (fun n : ℕ => 1 + ((n + 1 : ℕ) : ℝ)⁻¹)
        atTop (nhds 1) := by
      simpa only [add_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).add hninv
    apply hh.congr'
    filter_upwards [] with n
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hn] <;> ring
  have hrecip := reciprocal_successive_ratio_tendsto_zero a ha hpos hgrowth
  have hratio : Tendsto (fun n : ℕ => u (n + 1) / u n) atTop (nhds 0) := by
    have hz := (hlinear.pow 3).mul hrecip
    simp only [mul_zero] at hz
    apply hz.congr'
    filter_upwards [] with n
    have h0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
    have h1 : (a (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 1)).ne'
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    dsimp [u]
    field_simp [h0, h1, hn]
    <;> push_cast <;> ring
  have hu0 := positive_sequence_zero_of_ratio_zero u hu hratio
  apply squeeze_zero
    (fun n : ℕ => div_nonneg (by positivity) (by positivity)) _ hu0
  intro n
  apply div_le_div_of_nonneg_right _ (by positivity)
  gcongr
  exact_mod_cast Nat.le_succ n
