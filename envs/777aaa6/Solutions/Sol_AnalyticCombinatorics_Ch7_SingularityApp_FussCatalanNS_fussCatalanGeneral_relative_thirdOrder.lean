-- Prove2me | solution 1 for AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanNS.fussCatalanGeneral_relative_thirdOrder
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T00:58:45.179052+00:00
-- url     : https://prove2.me/submissions/60cb9c46-ca75-49ff-98fa-816410a45076

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_CayleyThirdOrder
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_TernaryTrees
import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_FussCatalanGeneralThirdOrder
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Third-order Cayley tree-function coefficient asymptotic

This file extends the Stirling route from `CayleySecondOrder` by one relative
order.  The sharper log-tail squeeze is

`1/(12n) - 1/n^3 ≤ log (stirlingSeq n / sqrt pi) ≤ 1/(12n)`,

which is enough to exponentiate `-log (stirlingSeq n / sqrt pi)` through the
quadratic term.  The third relative Cayley coefficient is `1/288`.
-/

set_option maxHeartbeats 1200000

open Filter Asymptotics
open scoped Topology BigOperators

namespace AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

noncomputable section

private lemma stirlingSeq_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < Stirling.stirlingSeq n := by
  cases n with
  | zero => cases hn
  | succ n => simpa using Stirling.stirlingSeq'_pos n

private lemma stirlingLog_tendsto_log_sqrt_pi :
    Tendsto stirlingLog atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
  have hlog :=
    (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  simpa [stirlingLog] using hlog

private lemma stirlingLogCorr_tendsto_zero :
    Tendsto stirlingLogCorr atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (1 / 12 : ℝ) * (n : ℝ)⁻¹) atTop (𝓝 0)
  simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 12 : ℝ)

private lemma inv_nat_cube_tendsto_zero :
    Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) atTop (𝓝 0) := by
  simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 3

private lemma stirlingLogCorrLower_tendsto_zero :
    Tendsto stirlingLogCorrLower atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => stirlingLogCorr n - ((n : ℝ)⁻¹) ^ 3) atTop (𝓝 0)
  simpa [sub_zero] using stirlingLogCorr_tendsto_zero.sub inv_nat_cube_tendsto_zero

private lemma stirlingLogCorr_sub_succ (n : ℕ) (hn : n ≠ 0) :
    stirlingLogCorr n - stirlingLogCorr (n + 1) =
      1 / (12 * (n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn1R : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold stirlingLogCorr
  field_simp [hnR, hn1R]
  norm_num [Nat.cast_add]

private lemma stirlingLog_diff_le_corr_diff {n : ℕ} (hn : 1 ≤ n) :
    stirlingLog n - stirlingLog (n + 1) ≤
      stirlingLogCorr n - stirlingLogCorr (n + 1) := by
  have hn0 : n ≠ 0 := by omega
  rw [stirlingLogCorr_sub_succ n hn0]
  /- Positive-index branch adapted from Mathlib's original pinned
  `Stirling.log_stirlingSeq_diff_le` (8a178386ffc0f5fef0b77738bb5449d50efeea95).
  Copyright (c) 2022 Moritz Firsching; authors Moritz Firsching, Fabian Kruse,
  Nikolas Kuhn. Released under Apache 2.0, as in Mathlib/LICENSE. -/
  have hupper (k : ℕ) :
      Real.log (Stirling.stirlingSeq (k + 1)) -
          Real.log (Stirling.stirlingSeq (k + 2)) ≤
        (1 : ℝ) / (12 * (k + 1 : ℕ) * ((k + 1 : ℕ) + 1)) := by
    set r := ((1 : ℝ) / (2 * (k + 1) + 1)) ^ 2 with hr
    have hr1 : r < 1 := by grw [hr, ← k.zero_le]; norm_num
    suffices HasSum (fun j : ℕ => r ^ (j + 1) / 3)
        ((1 : ℝ) / (12 * (k + 1 : ℕ) * ((k + 1 : ℕ) + 1))) by
      refine hasSum_le (fun j => ?_) (Stirling.log_stirlingSeq_diff_hasSum k) this
      simpa [hr, field] using show (3 : ℝ) ≤ 2 * (j + 1) + 1 by norm_cast; grind
    grind [((hasSum_geometric_of_lt_one (by positivity) hr1).mul_right r).div_const 3]
  have hsub1 : (n - 1 + 1 : ℕ) = n := Nat.sub_add_cancel hn
  have hsub2 : (n - 1 + 2 : ℕ) = n + 1 := by omega
  simpa [stirlingLog, hsub1, hsub2] using hupper (n - 1)

private lemma stirlingLog_diff_first_term_le {n : ℕ} (hn : 1 ≤ n) :
    1 / (3 * (2 * (n : ℝ) + 1) ^ 2) ≤
      stirlingLog n - stirlingLog (n + 1) := by
  classical
  let f : ℕ → ℝ := fun j =>
    (1 : ℝ) / (2 * ((j + 1 : ℕ) : ℝ) + 1) *
      (((1 : ℝ) / (2 * (((n - 1 : ℕ) + 1 : ℕ) : ℝ) + 1)) ^ 2) ^ (j + 1)
  have hsum : HasSum f (stirlingLog n - stirlingLog (n + 1)) := by
    have hraw := Stirling.log_stirlingSeq_diff_hasSum (n - 1)
    have hsub1 : (n - 1 + 1 : ℕ) = n := Nat.sub_add_cancel hn
    have hsub2 : (n - 1 + 2 : ℕ) = n + 1 := by omega
    simpa [f, stirlingLog, hsub1, hsub2] using hraw
  have hfirst : f 0 ≤ stirlingLog n - stirlingLog (n + 1) := by
    refine le_hasSum hsum 0 ?_
    intro j _hj
    positivity
  have hf0 : f 0 = 1 / (3 * (2 * (n : ℝ) + 1) ^ 2) := by
    have hsub1 : (n - 1 + 1 : ℕ) = n := Nat.sub_add_cancel hn
    unfold f
    rw [hsub1]
    norm_num
    field_simp
  simpa [hf0] using hfirst

private lemma stirlingLogCorrLower_step_le_first {n : ℕ} (hn : 1 ≤ n) :
    stirlingLogCorrLower n - stirlingLogCorrLower (n + 1) ≤
      1 / (3 * (2 * (n : ℝ) + 1) ^ 2) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (1 : ℕ)) hn)
  have hn1pos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have htwopos : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hn0 : n ≠ 0 := by omega
  have hdiff :
      1 / (12 * (n : ℝ) * ((n + 1 : ℕ) : ℝ)) -
          1 / (3 * (2 * (n : ℝ) + 1) ^ 2) =
        1 / (12 * (n : ℝ) * ((n + 1 : ℕ) : ℝ) *
          (2 * (n : ℝ) + 1) ^ 2) := by
    field_simp [hnpos.ne', hn1pos.ne', htwopos.ne']
    norm_num [Nat.cast_add]
    ring
  have hcube :
      1 / (12 * (n : ℝ) * ((n + 1 : ℕ) : ℝ) *
          (2 * (n : ℝ) + 1) ^ 2) ≤
        ((n : ℝ)⁻¹) ^ 3 - (((n + 1 : ℕ) : ℝ)⁻¹) ^ 3 := by
    field_simp [hnpos.ne', hn1pos.ne', htwopos.ne']
    norm_num [Nat.cast_add]
    nlinarith [sq_nonneg (n : ℝ), hnpos]
  unfold stirlingLogCorrLower
  rw [show stirlingLogCorr n - (n : ℝ)⁻¹ ^ 3 -
        (stirlingLogCorr (n + 1) - (((n + 1 : ℕ) : ℝ)⁻¹) ^ 3) =
      (stirlingLogCorr n - stirlingLogCorr (n + 1)) -
        (((n : ℝ)⁻¹) ^ 3 - (((n + 1 : ℕ) : ℝ)⁻¹) ^ 3) by ring]
  rw [stirlingLogCorr_sub_succ n hn0]
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
  rw [hdiff]
  exact hcube

private lemma stirlingLogCorrLower_step {n : ℕ} (hn : 1 ≤ n) :
    stirlingLogCorrLower n - stirlingLogCorrLower (n + 1) ≤
      stirlingLog n - stirlingLog (n + 1) := by
  exact le_trans (stirlingLogCorrLower_step_le_first hn)
    (stirlingLog_diff_first_term_le hn)

private lemma stirlingLogTail_upper_finite {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    stirlingLog n - stirlingLog m ≤ stirlingLogCorr n - stirlingLogCorr m := by
  induction m, hnm using Nat.le_induction with
  | base =>
      simp
  | succ m hnm ih =>
      have hm : 1 ≤ m := le_trans hn hnm
      have hstep := stirlingLog_diff_le_corr_diff hm
      calc
        stirlingLog n - stirlingLog (m + 1)
            = (stirlingLog n - stirlingLog m) +
                (stirlingLog m - stirlingLog (m + 1)) := by ring
        _ ≤ (stirlingLogCorr n - stirlingLogCorr m) +
              (stirlingLogCorr m - stirlingLogCorr (m + 1)) := by
                exact add_le_add ih hstep
        _ = stirlingLogCorr n - stirlingLogCorr (m + 1) := by ring

private lemma stirlingLogTail_lower_finite {n m : ℕ} (hn : 1 ≤ n) (hnm : n ≤ m) :
    stirlingLogCorrLower n - stirlingLogCorrLower m ≤
      stirlingLog n - stirlingLog m := by
  induction m, hnm using Nat.le_induction with
  | base =>
      simp
  | succ m hnm ih =>
      have hm : 1 ≤ m := le_trans hn hnm
      have hstep := stirlingLogCorrLower_step hm
      calc
        stirlingLogCorrLower n - stirlingLogCorrLower (m + 1)
            = (stirlingLogCorrLower n - stirlingLogCorrLower m) +
                (stirlingLogCorrLower m - stirlingLogCorrLower (m + 1)) := by ring
        _ ≤ (stirlingLog n - stirlingLog m) +
              (stirlingLog m - stirlingLog (m + 1)) := by
                exact add_le_add ih hstep
        _ = stirlingLog n - stirlingLog (m + 1) := by ring

private lemma stirlingLogTail_upper {n : ℕ} (hn : 1 ≤ n) :
    stirlingLogTail n ≤ stirlingLogCorr n := by
  have hleft : Tendsto (fun m : ℕ => stirlingLog n - stirlingLog m) atTop
      (𝓝 (stirlingLogTail n)) := by
    simpa [stirlingLogTail] using tendsto_const_nhds.sub stirlingLog_tendsto_log_sqrt_pi
  have hright : Tendsto (fun m : ℕ => stirlingLogCorr n - stirlingLogCorr m) atTop
      (𝓝 (stirlingLogCorr n)) := by
    simpa using tendsto_const_nhds.sub stirlingLogCorr_tendsto_zero
  exact le_of_tendsto_of_tendsto hleft hright
    (eventually_atTop.mpr ⟨n, fun m hm => stirlingLogTail_upper_finite hn hm⟩)

private lemma stirlingLogTail_lower {n : ℕ} (hn : 1 ≤ n) :
    stirlingLogCorrLower n ≤ stirlingLogTail n := by
  have hleft : Tendsto (fun m : ℕ => stirlingLogCorrLower n - stirlingLogCorrLower m)
      atTop (𝓝 (stirlingLogCorrLower n)) := by
    simpa using tendsto_const_nhds.sub stirlingLogCorrLower_tendsto_zero
  have hright : Tendsto (fun m : ℕ => stirlingLog n - stirlingLog m) atTop
      (𝓝 (stirlingLogTail n)) := by
    simpa [stirlingLogTail] using tendsto_const_nhds.sub stirlingLog_tendsto_log_sqrt_pi
  exact le_of_tendsto_of_tendsto hleft hright
    (eventually_atTop.mpr ⟨n, fun m hm => stirlingLogTail_lower_finite hn hm⟩)

private lemma inv_nat_sq_isBigO_inv :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) =O[atTop] fun n : ℕ => (n : ℝ)⁻¹ := by
  refine IsBigO.of_bound 1 ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  have hinv_le_one : (n : ℝ)⁻¹ ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact inv_le_one_of_one_le₀ hn1
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 2),
    Real.norm_of_nonneg hinv_nonneg]
  nlinarith [mul_le_mul_of_nonneg_right hinv_le_one hinv_nonneg]

private lemma inv_nat_cube_isLittleO_inv_sq :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) =o[atTop]
      fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine IsLittleO.of_bound ?_
  intro c hc
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ < c :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (Iio_mem_nhds hc)
  filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hninvc
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 3),
    Real.norm_of_nonneg (pow_nonneg hinv_nonneg 2)]
  calc
    ((n : ℝ)⁻¹) ^ 3 = (n : ℝ)⁻¹ * ((n : ℝ)⁻¹) ^ 2 := by ring
    _ ≤ c * ((n : ℝ)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_of_lt hninvc) (pow_nonneg hinv_nonneg 2)

theorem stirlingLogTail_thirdOrder :
    (fun n : ℕ => stirlingLogTail n - stirlingLogCorr n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hcube := inv_nat_cube_isLittleO_inv_sq
  rw [Asymptotics.isLittleO_iff] at hcube ⊢
  intro c hc
  have hcubec := hcube hc
  filter_upwards [eventually_ge_atTop 1, hcubec] with n hn hcubec_n
  have hupper := stirlingLogTail_upper hn
  have hlower := stirlingLogTail_lower hn
  have hnonpos : stirlingLogTail n - stirlingLogCorr n ≤ 0 := by linarith
  have hbound : stirlingLogCorr n - stirlingLogTail n ≤ ((n : ℝ)⁻¹) ^ 3 := by
    unfold stirlingLogCorrLower at hlower
    linarith
  calc
    ‖stirlingLogTail n - stirlingLogCorr n‖
        = stirlingLogCorr n - stirlingLogTail n := by
            rw [Real.norm_of_nonpos hnonpos]
            ring
    _ ≤ ((n : ℝ)⁻¹) ^ 3 := hbound
    _ = ‖((n : ℝ)⁻¹) ^ 3‖ := by
          rw [Real.norm_of_nonneg (by positivity)]
    _ ≤ c * ‖((n : ℝ)⁻¹) ^ 2‖ := hcubec_n

private lemma stirlingLogTail_tendsto_zero :
    Tendsto stirlingLogTail atTop (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ => Real.log (Real.sqrt Real.pi)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) := tendsto_const_nhds
  have h := stirlingLog_tendsto_log_sqrt_pi.sub hconst
  simpa [stirlingLogTail, sub_self] using h

private lemma stirlingLogCorr_isBigO_inv :
    stirlingLogCorr =O[atTop] fun n : ℕ => (n : ℝ)⁻¹ := by
  exact (isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop).const_mul_left (1 / 12 : ℝ)

private lemma stirlingLogTail_isBigO_inv :
    stirlingLogTail =O[atTop] fun n : ℕ => (n : ℝ)⁻¹ := by
  have hsmallO : (fun n : ℕ => stirlingLogTail n - stirlingLogCorr n)
      =O[atTop] fun n : ℕ => (n : ℝ)⁻¹ :=
    stirlingLogTail_thirdOrder.isBigO.trans inv_nat_sq_isBigO_inv
  have hsum := hsmallO.add stirlingLogCorr_isBigO_inv
  refine hsum.congr_left ?_
  intro n
  ring

private lemma neg_stirlingLogTail_sq_isBigO_inv_sq :
    (fun n : ℕ => (-stirlingLogTail n) ^ 2) =O[atTop]
      fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hxO : (fun n : ℕ => -stirlingLogTail n) =O[atTop]
      fun n : ℕ => (n : ℝ)⁻¹ := by
    refine (stirlingLogTail_isBigO_inv.const_mul_left (-1)).congr_left ?_
    intro n
    ring
  have hsq := hxO.mul hxO
  refine hsq.congr' ?_ ?_
  · exact Eventually.of_forall fun n => by ring
  · exact Eventually.of_forall fun n => by ring

private lemma exp_neg_stirlingLogTail_thirdOrder_corr :
    (fun n : ℕ =>
      Real.exp (-stirlingLogTail n) -
        (1 - stirlingLogCorr n + (stirlingLogCorr n) ^ 2 / 2))
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  let x : ℕ → ℝ := fun n => -stirlingLogTail n
  let a : ℕ → ℝ := fun n => -stirlingLogCorr n
  have hx0 : Tendsto x atTop (𝓝 0) := by
    simpa [x] using stirlingLogTail_tendsto_zero.neg
  have ha0 : Tendsto a atTop (𝓝 0) := by
    simpa [a] using stirlingLogCorr_tendsto_zero.neg
  have hremLocal :
      (fun n : ℕ => Real.exp (x n) - (1 + x n + (x n) ^ 2 / 2))
        =o[atTop] fun n : ℕ => (x n) ^ 2 := by
    have h := (Real.exp_sub_sum_range_succ_isLittleO_pow 2).comp_tendsto hx0
    simpa [Finset.sum_range_succ] using h
  have hrem :
      (fun n : ℕ => Real.exp (x n) - (1 + x n + (x n) ^ 2 / 2))
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 :=
    hremLocal.trans_isBigO neg_stirlingLogTail_sq_isBigO_inv_sq
  have hdiff :
      (fun n : ℕ => x n - a n) =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    have h := stirlingLogTail_thirdOrder.const_mul_left (-1)
    refine h.congr_left ?_
    intro n
    simp [x, a]
    ring
  have hplusO : (fun n : ℕ => x n + a n) =O[atTop] fun _n : ℕ => (1 : ℝ) := by
    exact (hx0.add ha0).isBigO_one ℝ
  have hprod :
      (fun n : ℕ => (x n - a n) * (x n + a n) / 2)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    have h := hdiff.mul_isBigO hplusO
    have h' : (fun n : ℕ => (x n - a n) * (x n + a n))
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
      refine h.congr_right ?_
      intro n
      ring
    exact (h'.const_mul_left (1 / 2 : ℝ)).congr_left fun n => by ring
  have hpoly :
      (fun n : ℕ =>
        (1 + x n + (x n) ^ 2 / 2) - (1 + a n + (a n) ^ 2 / 2))
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    have hsum := hdiff.add hprod
    refine hsum.congr_left ?_
    intro n
    ring
  have htotal := hrem.add hpoly
  refine htotal.congr_left ?_
  intro n
  simp [x, a]
  ring

private lemma exp_neg_stirlingLogTail_thirdOrder :
    (fun n : ℕ =>
      Real.exp (-stirlingLogTail n) -
        (1 + cayleyRelativeSecondConstant * (n : ℝ)⁻¹ +
          cayleyRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine exp_neg_stirlingLogTail_thirdOrder_corr.congr_left ?_
  intro n
  unfold stirlingLogCorr cayleyRelativeSecondConstant cayleyRelativeThirdConstant
  ring

private lemma exp_neg_stirlingLogTail_eq_ratio {n : ℕ} (hn : 0 < n) :
    Real.exp (-stirlingLogTail n) =
      Real.sqrt Real.pi / Stirling.stirlingSeq n := by
  have hS : 0 < Stirling.stirlingSeq n := stirlingSeq_pos_of_pos hn
  have hπ : 0 < Real.sqrt Real.pi := by positivity
  unfold stirlingLogTail stirlingLog
  rw [neg_sub, Real.exp_sub, Real.exp_log hπ, Real.exp_log hS]

theorem stirlingSeq_inv_ratio_thirdOrder :
    (fun n : ℕ =>
      Real.sqrt Real.pi / Stirling.stirlingSeq n -
        (1 + cayleyRelativeSecondConstant * (n : ℝ)⁻¹ +
          cayleyRelativeThirdConstant * ((n : ℝ)⁻¹) ^ 2))
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine exp_neg_stirlingLogTail_thirdOrder.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [exp_neg_stirlingLogTail_eq_ratio hn]

end
end AnalyticCombinatorics.Ch7.SingularityApp.TreeFunctionNS

/-!
# Ternary trees and the Fuss-Catalan asymptotic

The number of full ternary trees with `n` internal nodes is
`1 / (2n + 1) * binom(3n,n)`.  This file proves the corresponding
Fuss-Catalan asymptotic directly from Stirling's formula.
-/

open Filter Asymptotics
open scoped Topology

lemma rpow_three_halves_mul_nat_real (n : ℕ) (hn : n ≠ 0) :
    (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  nth_rw 2 [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_add hnpos]
  norm_num

/-!
# General Fuss-Catalan asymptotic

For fixed `p ≥ 2`, this file derives the Fuss-Catalan asymptotic
from Stirling's formula:

`1 / ((p - 1)n + 1) * choose (pn) n`
is equivalent to
`C_p * r_p^n * n^(-3/2)`, with
`r_p = p^p / (p - 1)^(p - 1)` and
`C_p = sqrt p / ((p - 1)^(3/2) sqrt (2π))`.
-/

open Filter Asymptotics
open scoped Topology

lemma fussCatalan_succ_choose_dvd (q n : ℕ) :
    q * n + 1 ∣ Nat.choose ((q + 1) * n) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hrel := Nat.choose_succ_right_eq ((q + 1) * n) (n - 1)
    have hpred : n - 1 + 1 = n := Nat.sub_one_add_one hn
    have hsub : (q + 1) * n - (n - 1) = q * n + 1 := by
      rw [Nat.succ_mul]
      omega
    rw [hpred, hsub] at hrel
    have hdvd : q * n + 1 ∣ Nat.choose ((q + 1) * n) n * n := by
      rw [hrel, mul_comm]
      exact dvd_mul_left _ _
    have hcop : Nat.Coprime (q * n + 1) n := by
      have h : q * n + 1 = n * q + 1 := by
        rw [Nat.mul_comm q n]
      rw [h]
      exact (Nat.coprime_mul_left_add_left 1 n q).2 (by simp)
    exact hcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hdvd)

theorem fussCatalan_choose_dvd (p n : ℕ) (hp : 2 ≤ p) :
    (p - 1) * n + 1 ∣ Nat.choose (p * n) n := by
  have hq : 1 ≤ p - 1 := by omega
  have hpq : p - 1 + 1 = p := by omega
  simpa [hpq] using fussCatalan_succ_choose_dvd (p - 1) n

lemma fussCatalan_cast (p n : ℕ) (hp : 2 ≤ p) :
    (fussCatalan p n : ℝ) =
      ((Nat.choose (p * n) n : ℕ) : ℝ) / ((((p - 1) * n + 1 : ℕ) : ℝ)) := by
  unfold fussCatalan
  exact Nat.cast_div (fussCatalan_choose_dvd p n hp) (by positivity)

lemma choose_succ_mul_cast (q n : ℕ) :
    ((Nat.choose ((q + 1) * n) n : ℕ) : ℝ) =
      (((((q + 1) * n).factorial : ℕ) : ℝ) /
        ((((n.factorial : ℕ) : ℝ) * ((((q * n).factorial : ℕ) : ℝ))))) := by
  have hle : n ≤ (q + 1) * n := by
    rw [Nat.succ_mul]
    omega
  rw [Nat.cast_choose ℝ hle]
  have hsub : (q + 1) * n - n = q * n := by
    rw [Nat.succ_mul]
    omega
  rw [hsub]

lemma tendsto_const_mul_atTop (a : ℕ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => a * n) atTop atTop := by
  simpa [nsmul_eq_mul] using
    ((tendsto_id : Tendsto (fun n : ℕ => n) atTop atTop).nsmul_atTop ha)

lemma power_ratio_core_succ (n q : ℕ) (y : ℝ) (hy : y ≠ 0) (hq : (q : ℝ) ≠ 0) :
    ((((q + 1 : ℕ) : ℝ) * y) ^ ((q + 1) * n)) /
      (y ^ n * (((q : ℝ) * y) ^ (q * n))) =
      ((((q + 1 : ℕ) : ℝ) ^ (q + 1)) / ((q : ℝ) ^ q)) ^ n := by
  rw [pow_mul (((q + 1 : ℕ) : ℝ) * y) (q + 1) n,
    pow_mul ((q : ℝ) * y) q n]
  rw [mul_pow, mul_pow, div_pow]
  field_simp [pow_ne_zero n hy, pow_ne_zero (q * n) hy, pow_ne_zero q hq,
    pow_ne_zero n (pow_ne_zero q hq), pow_ne_zero (q * n) hq]
  rw [pow_succ, mul_pow]
  ring_nf

lemma stirling_power_ratio_succ (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    ((((((q + 1) * n : ℕ) : ℝ) / Real.exp 1) ^ ((q + 1) * n)) /
      ((((n : ℝ) / Real.exp 1) ^ n) *
        (((((q * n : ℕ) : ℝ) / Real.exp 1)) ^ (q * n)))) =
      fussCatalanBase (q + 1) ^ n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hE : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have hy : (n : ℝ) / Real.exp 1 ≠ 0 := div_ne_zero hnR hE
  have hqR : (q : ℝ) ≠ 0 := by positivity
  rw [show ((((q + 1) * n : ℕ) : ℝ) / Real.exp 1) =
      (((q + 1 : ℕ) : ℝ)) * ((n : ℝ) / Real.exp 1) by
        norm_num [Nat.cast_mul]
        ring,
    show ((((q * n : ℕ) : ℝ) / Real.exp 1)) =
      (q : ℝ) * ((n : ℝ) / Real.exp 1) by
        norm_num [Nat.cast_mul]
        ring]
  rw [power_ratio_core_succ n q ((n : ℝ) / Real.exp 1) hy hqR]
  simp [fussCatalanBase]

lemma stirling_sqrt_ratio_succ (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    Real.sqrt (2 * (((q + 1) * n : ℕ) : ℝ) * Real.pi) /
      (Real.sqrt (2 * (n : ℝ) * Real.pi) *
        Real.sqrt (2 * ((q * n : ℕ) : ℝ) * Real.pi)) =
    Real.sqrt (((q + 1 : ℕ) : ℝ)) /
      (Real.sqrt ((q : ℝ)) * Real.sqrt (2 * Real.pi * (n : ℝ))) := by
  have hnum : Real.sqrt (2 * (((q + 1) * n : ℕ) : ℝ) * Real.pi) =
      Real.sqrt (((q + 1 : ℕ) : ℝ)) * Real.sqrt (2 * (n : ℝ) * Real.pi) := by
    rw [show 2 * (((q + 1) * n : ℕ) : ℝ) * Real.pi =
        (((q + 1 : ℕ) : ℝ)) * (2 * (n : ℝ) * Real.pi) by
          norm_num [Nat.cast_mul]
          ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ (((q + 1 : ℕ) : ℝ)))]
  have hden2 : Real.sqrt (2 * ((q * n : ℕ) : ℝ) * Real.pi) =
      Real.sqrt ((q : ℝ)) * Real.sqrt (2 * (n : ℝ) * Real.pi) := by
    rw [show 2 * ((q * n : ℕ) : ℝ) * Real.pi =
        (q : ℝ) * (2 * (n : ℝ) * Real.pi) by
          norm_num [Nat.cast_mul]
          ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ (q : ℝ))]
  have hA_ne : Real.sqrt (2 * (n : ℝ) * Real.pi) ≠ 0 := by positivity
  have hq_ne : Real.sqrt (q : ℝ) ≠ 0 := by positivity
  rw [hnum, hden2]
  rw [show 2 * (n : ℝ) * Real.pi = 2 * Real.pi * (n : ℝ) by ring]
  field_simp [hA_ne, hq_ne]

lemma stirling_choose_scale_succ_eq (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    stirlingScale ((q + 1) * n) / (stirlingScale n * stirlingScale (q * n)) =
      fussCatalanChooseScale (q + 1) n := by
  unfold stirlingScale fussCatalanChooseScale
  rw [show
      (Real.sqrt (2 * ↑((q + 1) * n) * Real.pi) *
            (↑((q + 1) * n) / Real.exp 1) ^ ((q + 1) * n)) /
          ((Real.sqrt (2 * ↑n * Real.pi) * (↑n / Real.exp 1) ^ n) *
            (Real.sqrt (2 * ↑(q * n) * Real.pi) *
              (↑(q * n) / Real.exp 1) ^ (q * n))) =
        (Real.sqrt (2 * ↑((q + 1) * n) * Real.pi) /
          (Real.sqrt (2 * ↑n * Real.pi) * Real.sqrt (2 * ↑(q * n) * Real.pi))) *
        (((↑((q + 1) * n) / Real.exp 1) ^ ((q + 1) * n)) /
          (((↑n / Real.exp 1) ^ n) * ((↑(q * n) / Real.exp 1) ^ (q * n)))) by
        ring_nf]
  rw [stirling_sqrt_ratio_succ q n hq hn, stirling_power_ratio_succ q n hq hn]
  simp only [Nat.add_sub_cancel]
  ring_nf

lemma sqrt_two_pi_mul_nat_eq_sqrt_two_pi_mul_rpow_real (n : ℕ) (hn : n ≠ 0) :
    Real.sqrt (2 * Real.pi * (n : ℝ)) * (n : ℝ) =
      Real.sqrt (2 * Real.pi) * ((n : ℝ) ^ (3 / 2 : ℝ)) := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [mul_assoc, rpow_three_halves_mul_nat_real n hn]

lemma sqrt_nat_mul_nat_eq_rpow_three_halves (q : ℕ) (hq : q ≠ 0) :
    Real.sqrt (q : ℝ) * (q : ℝ) = (q : ℝ) ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  exact rpow_three_halves_mul_nat_real q hq

lemma fussCatalan_scale_succ_simplified (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    fussCatalanChooseScale (q + 1) n / ((q : ℝ) * (n : ℝ)) =
      fussCatalanConst (q + 1) * fussCatalanBase (q + 1) ^ n *
        ((n : ℝ) ^ (-(3 / 2) : ℝ)) := by
  unfold fussCatalanChooseScale fussCatalanConst
  simp only [Nat.add_sub_cancel]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hqne : q ≠ 0 := by omega
  have hn32_ne : (n : ℝ) ^ (3 / 2 : ℝ) ≠ 0 := by positivity
  have hq32_ne : (q : ℝ) ^ (3 / 2 : ℝ) ≠ 0 := by positivity
  have hsqrt2pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  rw [div_div]
  rw [show Real.sqrt (q : ℝ) * Real.sqrt (2 * Real.pi * (n : ℝ)) *
      ((q : ℝ) * (n : ℝ)) =
        (Real.sqrt (q : ℝ) * (q : ℝ)) *
          (Real.sqrt (2 * Real.pi * (n : ℝ)) * (n : ℝ)) by ring]
  rw [sqrt_nat_mul_nat_eq_rpow_three_halves q hqne,
    sqrt_two_pi_mul_nat_eq_sqrt_two_pi_mul_rpow_real n hn]
  rw [Real.rpow_neg hnpos.le]
  field_simp [hn32_ne, hq32_ne, hsqrt2pi_ne]

/-!
# Third-order Fuss-Catalan coefficient asymptotic, fixed general arity

This file proves the relative third-order asymptotic for the closed form

`1 / ((p - 1)n + 1) * binom (pn) n`.

The only analytic input is the third-order Stirling-sequence expansion already
proved in `CayleyThirdOrder`, applied at `n`, `(p - 1)n`, and `pn`.
-/

set_option maxHeartbeats 1600000

open Filter Asymptotics
open scoped Topology

namespace AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanNS

noncomputable section

private lemma stirlingSeq_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < Stirling.stirlingSeq n := by
  cases n with
  | zero => cases hn
  | succ n => simpa using Stirling.stirlingSeq'_pos n

private lemma inv_nat_cube_isLittleO_inv_sq :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 3) =o[atTop]
      fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine IsLittleO.of_bound ?_
  intro c hc
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ < c :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (Iio_mem_nhds hc)
  filter_upwards [eventually_ge_atTop 1, hsmall] with n hn hninvc
  have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
  rw [Real.norm_of_nonneg (pow_nonneg hinv_nonneg 3),
    Real.norm_of_nonneg (pow_nonneg hinv_nonneg 2)]
  calc
    ((n : ℝ)⁻¹) ^ 3 = (n : ℝ)⁻¹ * ((n : ℝ)⁻¹) ^ 2 := by ring
    _ ≤ c * ((n : ℝ)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_right (le_of_lt hninvc) (pow_nonneg hinv_nonneg 2)

private lemma inv_nat_four_isLittleO_inv_sq :
    (fun n : ℕ => ((n : ℝ)⁻¹) ^ 4) =o[atTop]
      fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hO : (fun n : ℕ => (n : ℝ)⁻¹) =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).isBigO_one ℝ
  have h := inv_nat_cube_isLittleO_inv_sq.mul_isBigO hO
  simpa [Pi.mul_apply, mul_assoc] using h.congr_left (fun n => by ring)

private lemma const_mul_inv_sq_isBigO_inv_sq (a : ℕ) (ha : 0 < a) :
    (fun n : ℕ => ((((a * n : ℕ) : ℝ) ^ 2)⁻¹))
      =O[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine IsBigO.of_bound ((a : ℝ)⁻¹ ^ 2) ?_
  refine eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hn))
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ ((((a * n : ℕ) : ℝ) ^ 2)⁻¹)),
    Real.norm_of_nonneg (pow_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹) 2)]
  rw [show ((((a * n : ℕ) : ℝ) ^ 2)⁻¹) =
      ((a : ℝ)⁻¹ ^ 2) * ((n : ℝ)⁻¹) ^ 2 by
    norm_num [Nat.cast_mul]
    field_simp [haR, hnR]]

private lemma stirlingInvRatio_constMul_tendsto_one (a : ℕ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => stirlingInvRatio (a * n)) atTop (𝓝 1) := by
  have hseq :
      Tendsto (fun n : ℕ => Stirling.stirlingSeq (a * n)) atTop
        (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_const_mul_atTop a ha)
  have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
  have hconst : Tendsto (fun _n : ℕ => Real.sqrt Real.pi) atTop
      (𝓝 (Real.sqrt Real.pi)) := tendsto_const_nhds
  simpa [stirlingInvRatio, div_self hsqrt] using hconst.div hseq hsqrt

private lemma stirlingInvRatio_constMul_thirdOrder (a : ℕ) (ha : 0 < a) :
    (fun n : ℕ =>
      stirlingInvRatio (a * n) - stirlingInvRatioApprox a n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hraw :=
    TreeFunctionNS.stirlingSeq_inv_ratio_thirdOrder.comp_tendsto
      (tendsto_const_mul_atTop a ha)
  have htarget := hraw.trans_isBigO (by
    simpa [Function.comp_def] using const_mul_inv_sq_isBigO_inv_sq a ha)
  have hleft :
      (fun n : ℕ =>
        stirlingInvRatio (a * n) - stirlingInvRatioApprox a n)
        =o[atTop] fun n : ℕ => (((n : ℝ) ^ 2)⁻¹) := by
    refine htarget.congr_left ?_
    intro n
    unfold stirlingInvRatio stirlingInvRatioApprox
    unfold TreeFunctionNS.cayleyRelativeSecondConstant
      TreeFunctionNS.cayleyRelativeThirdConstant
    by_cases hn : n = 0
    · subst n
      simp [Stirling.stirlingSeq_zero]
    · have haR : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      norm_num [Nat.cast_mul]
      field_simp [haR, hnR]
      ring_nf
  simpa [inv_pow] using hleft

private lemma poly2_tendsto_one (a b : ℝ) :
    Tendsto (fun n : ℕ => poly2 a b n) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using h1.pow 2
  simpa [poly2] using (tendsto_const_nhds.add (h1.const_mul a)).add (h2.const_mul b)

private lemma product_two_sub_product_two_isLittleO
    {f g F G : ℕ → ℝ}
    (hf : (fun n : ℕ => f n - F n) =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2)
    (hg : (fun n : ℕ => g n - G n) =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2)
    (hgO : g =O[atTop] fun _n : ℕ => (1 : ℝ))
    (hFO : F =O[atTop] fun _n : ℕ => (1 : ℝ)) :
    (fun n : ℕ => f n * g n - F n * G n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have h1 := hf.mul_isBigO hgO
  have h2 := hg.mul_isBigO hFO
  have hsum := h1.add h2
  simpa [Pi.mul_apply] using hsum.congr_left (fun n => by ring)

private lemma poly2_mul_trunc_isLittleO (a b c d : ℝ) :
    (fun n : ℕ =>
      poly2 a b n * poly2 c d n - poly2 (a + c) (b + d + a * c) n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have h3 := inv_nat_cube_isLittleO_inv_sq.const_mul_left (a * d + b * c)
  have h4 := inv_nat_four_isLittleO_inv_sq.const_mul_left (b * d)
  have h := h3.add h4
  refine h.congr_left ?_
  intro n
  unfold poly2
  ring

private lemma poly2_div_trunc_residual_isLittleO (A B C D : ℝ) :
    (fun n : ℕ =>
      poly2 A B n - poly2 (A - C) (B - D - C * (A - C)) n * poly2 C D n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  let S : ℝ := A - C
  let T : ℝ := B - D - C * (A - C)
  have h3 := inv_nat_cube_isLittleO_inv_sq.const_mul_left (-(S * D + T * C))
  have h4 := inv_nat_four_isLittleO_inv_sq.const_mul_left (-(T * D))
  have h := h3.add h4
  refine h.congr_left ?_
  intro n
  unfold poly2
  simp [S, T]
  ring

private lemma stirlingInvRatioApprox_eq_poly2 (a n : ℕ) :
    stirlingInvRatioApprox a n = poly2 (stirlingLinear a) (stirlingQuadratic a) n := by
  unfold stirlingInvRatioApprox poly2 stirlingLinear stirlingQuadratic
  ring

private lemma stirlingProductApprox_eq_poly2 (p n : ℕ) :
    stirlingProductApprox p n =
      poly2 (fussCatalanGeneralStirlingC p)
        ((fussCatalanGeneralStirlingC p) ^ 2 / 2) n := by
  rfl

private lemma rationalPrefactorApprox_eq_poly2 (q n : ℕ) :
    rationalPrefactorApprox q n =
      poly2 (-(1 / (q : ℝ))) (1 / ((q : ℝ) ^ 2)) n := by
  unfold rationalPrefactorApprox poly2
  ring

private lemma stirlingProductApprox_tendsto_one (p : ℕ) :
    Tendsto (fun n : ℕ => stirlingProductApprox p n) atTop (𝓝 1) := by
  simpa [stirlingProductApprox_eq_poly2] using
    poly2_tendsto_one (fussCatalanGeneralStirlingC p)
      ((fussCatalanGeneralStirlingC p) ^ 2 / 2)

private lemma stirlingProduct_linear_eq (p : ℕ) (hp : 2 ≤ p) :
    (stirlingLinear 1 + stirlingLinear (p - 1)) - stirlingLinear p =
      fussCatalanGeneralStirlingC p := by
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hp))
  have hqR : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have hq : 0 < p - 1 := by omega
    exact_mod_cast Nat.ne_of_gt hq
  have hqcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  unfold stirlingLinear fussCatalanGeneralStirlingC
  field_simp [hpR, hqR]
  rw [hqcast]
  ring

private lemma stirlingProduct_quadratic_eq (p : ℕ) (hp : 2 ≤ p) :
    (stirlingQuadratic 1 + stirlingQuadratic (p - 1) +
        stirlingLinear 1 * stirlingLinear (p - 1)) -
        stirlingQuadratic p -
        stirlingLinear p *
          ((stirlingLinear 1 + stirlingLinear (p - 1)) - stirlingLinear p) =
      (fussCatalanGeneralStirlingC p) ^ 2 / 2 := by
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hp))
  have hqR : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have hq : 0 < p - 1 := by omega
    exact_mod_cast Nat.ne_of_gt hq
  have hqcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  unfold stirlingLinear stirlingQuadratic fussCatalanGeneralStirlingC
  field_simp [hpR, hqR]
  rw [hqcast]
  ring

private lemma stirlingProduct_quadratic_eq_stirlingC (p : ℕ) (hp : 2 ≤ p) :
    (stirlingQuadratic 1 + stirlingQuadratic (p - 1) +
        stirlingLinear 1 * stirlingLinear (p - 1)) -
        stirlingQuadratic p -
        stirlingLinear p * fussCatalanGeneralStirlingC p =
      (fussCatalanGeneralStirlingC p) ^ 2 / 2 := by
  calc
    (stirlingQuadratic 1 + stirlingQuadratic (p - 1) +
        stirlingLinear 1 * stirlingLinear (p - 1)) -
        stirlingQuadratic p -
        stirlingLinear p * fussCatalanGeneralStirlingC p =
      (stirlingQuadratic 1 + stirlingQuadratic (p - 1) +
        stirlingLinear 1 * stirlingLinear (p - 1)) -
        stirlingQuadratic p -
        stirlingLinear p *
          ((stirlingLinear 1 + stirlingLinear (p - 1)) - stirlingLinear p) := by
          rw [stirlingProduct_linear_eq p hp]
    _ = (fussCatalanGeneralStirlingC p) ^ 2 / 2 :=
      stirlingProduct_quadratic_eq p hp

private lemma stirlingInvProduct_thirdOrder (p : ℕ) (hp : 2 ≤ p) :
    (fun n : ℕ =>
      stirlingInvRatio n * stirlingInvRatio ((p - 1) * n) /
          stirlingInvRatio (p * n) -
        stirlingProductApprox p n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : 0 < 2) hp
  have hq0 : 0 < p - 1 := by omega
  have hA1 :
      (fun n : ℕ =>
        stirlingInvRatio n - poly2 (stirlingLinear 1) (stirlingQuadratic 1) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    simpa [stirlingInvRatioApprox_eq_poly2] using
      stirlingInvRatio_constMul_thirdOrder 1 (by norm_num)
  have hAq :
      (fun n : ℕ =>
        stirlingInvRatio ((p - 1) * n) -
          poly2 (stirlingLinear (p - 1)) (stirlingQuadratic (p - 1)) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    simpa [stirlingInvRatioApprox_eq_poly2] using
      stirlingInvRatio_constMul_thirdOrder (p - 1) hq0
  have hAp :
      (fun n : ℕ =>
        stirlingInvRatio (p * n) - poly2 (stirlingLinear p) (stirlingQuadratic p) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    simpa [stirlingInvRatioApprox_eq_poly2] using
      stirlingInvRatio_constMul_thirdOrder p hp0
  have hAqO :
      (fun n : ℕ => stirlingInvRatio ((p - 1) * n))
        =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    (stirlingInvRatio_constMul_tendsto_one (p - 1) hq0).isBigO_one ℝ
  have hP1O :
      (fun n : ℕ => poly2 (stirlingLinear 1) (stirlingQuadratic 1) n)
        =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    (poly2_tendsto_one (stirlingLinear 1) (stirlingQuadratic 1)).isBigO_one ℝ
  have hprod :=
    product_two_sub_product_two_isLittleO hA1 hAq hAqO hP1O
  let A : ℝ := stirlingLinear 1 + stirlingLinear (p - 1)
  let B : ℝ := stirlingQuadratic 1 + stirlingQuadratic (p - 1) +
    stirlingLinear 1 * stirlingLinear (p - 1)
  let C : ℝ := stirlingLinear p
  let D : ℝ := stirlingQuadratic p
  have hpolyProd :
      (fun n : ℕ =>
        poly2 (stirlingLinear 1) (stirlingQuadratic 1) n *
            poly2 (stirlingLinear (p - 1)) (stirlingQuadratic (p - 1)) n -
          poly2 A B n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    simpa [A, B] using
      poly2_mul_trunc_isLittleO (stirlingLinear 1) (stirlingQuadratic 1)
        (stirlingLinear (p - 1)) (stirlingQuadratic (p - 1))
  have hpolyDiv :
      (fun n : ℕ =>
        poly2 A B n -
          stirlingProductApprox p n * poly2 (stirlingLinear p) (stirlingQuadratic p) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    have hraw := poly2_div_trunc_residual_isLittleO A B C D
    simpa [A, B, C, D, stirlingProductApprox_eq_poly2,
      stirlingProduct_linear_eq p hp, stirlingProduct_quadratic_eq_stirlingC p hp] using hraw
  have hpoly := hpolyProd.add hpolyDiv
  have hpoly' :
      (fun n : ℕ =>
        poly2 (stirlingLinear 1) (stirlingQuadratic 1) n *
            poly2 (stirlingLinear (p - 1)) (stirlingQuadratic (p - 1)) n -
          stirlingProductApprox p n *
            poly2 (stirlingLinear p) (stirlingQuadratic p) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    refine hpoly.congr_left ?_
    intro n
    ring
  have hnumToApprox := hprod.add hpoly'
  have hnumToApprox' :
      (fun n : ℕ =>
        stirlingInvRatio n * stirlingInvRatio ((p - 1) * n) -
          stirlingProductApprox p n *
            poly2 (stirlingLinear p) (stirlingQuadratic p) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    refine hnumToApprox.congr_left ?_
    intro n
    ring
  have hSPO :
      (fun n : ℕ => stirlingProductApprox p n)
        =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    (stirlingProductApprox_tendsto_one p).isBigO_one ℝ
  have hdenErr0 := hAp.mul_isBigO hSPO
  have hdenErr :
      (fun n : ℕ =>
        stirlingProductApprox p n * stirlingInvRatio (p * n) -
          stirlingProductApprox p n *
            poly2 (stirlingLinear p) (stirlingQuadratic p) n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    simpa [Pi.mul_apply] using hdenErr0.congr_left (fun n => by ring)
  have hnum0 := hnumToApprox'.sub hdenErr
  have hnum :
      (fun n : ℕ =>
        stirlingInvRatio n * stirlingInvRatio ((p - 1) * n) -
          stirlingProductApprox p n * stirlingInvRatio (p * n))
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    refine hnum0.congr_left ?_
    intro n
    ring
  have hdenInvO :
      (fun n : ℕ => (stirlingInvRatio (p * n))⁻¹)
        =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    ((stirlingInvRatio_constMul_tendsto_one p hp0).inv₀ one_ne_zero).isBigO_one ℝ
  have hdiv0 := hnum.mul_isBigO hdenInvO
  refine hdiv0.congr' ?_ (Eventually.of_forall fun n => by ring)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hpnpos : 0 < p * n := Nat.mul_pos hp0 hn
  have hden : stirlingInvRatio (p * n) ≠ 0 := by
    unfold stirlingInvRatio
    exact div_ne_zero (by positivity) (stirlingSeq_pos_of_pos hpnpos).ne'
  field_simp [hden]

private lemma rationalPrefactorApprox_tendsto_one (q : ℕ) :
    Tendsto (fun n : ℕ => rationalPrefactorApprox q n) atTop (𝓝 1) := by
  simpa [rationalPrefactorApprox_eq_poly2] using
    poly2_tendsto_one (-(1 / (q : ℝ))) (((q : ℝ) ^ 2)⁻¹)

private lemma rationalPrefactor_thirdOrder (q : ℕ) (hq : 0 < q) :
    (fun n : ℕ => rationalPrefactor q n - rationalPrefactorApprox q n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hnat : Tendsto (fun n : ℕ => q * n + 1) atTop atTop := by
    simpa [Function.comp_def] using
      (tendsto_add_atTop_nat 1).comp (tendsto_const_mul_atTop q hq)
  have hinv_tend :
      Tendsto (fun n : ℕ => (((q * n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hnat
  have hinvLittle :
      (fun n : ℕ => (((q * n + 1 : ℕ) : ℝ)⁻¹))
        =o[atTop] fun _n : ℕ => (1 : ℝ) :=
    (isLittleO_one_iff ℝ).mpr hinv_tend
  have hx2O :
      (fun n : ℕ => ((n : ℝ)⁻¹) ^ 2)
        =O[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 :=
    isBigO_refl _ _
  have hprod := hinvLittle.mul_isBigO hx2O
  have hscaled := hprod.const_mul_left (-(1 / ((q : ℝ) ^ 2)))
  refine hscaled.congr' ?_ (Eventually.of_forall fun n => by ring)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hden : (((q * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  unfold rationalPrefactor rationalPrefactorApprox
  norm_num [Nat.cast_mul, Nat.cast_add]
  field_simp [hqR, hnR, hden]
  ring

private lemma stirlingInvProduct_tendsto_one (p : ℕ) (hp : 2 ≤ p) :
    Tendsto
      (fun n : ℕ =>
        stirlingInvRatio n * stirlingInvRatio ((p - 1) * n) /
          stirlingInvRatio (p * n))
      atTop (𝓝 1) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : 0 < 2) hp
  have hq0 : 0 < p - 1 := by omega
  have h1 : Tendsto (fun n : ℕ => stirlingInvRatio n) atTop (𝓝 1) := by
    simpa using stirlingInvRatio_constMul_tendsto_one 1 (by norm_num)
  have hq := stirlingInvRatio_constMul_tendsto_one (p - 1) hq0
  have hp' := stirlingInvRatio_constMul_tendsto_one p hp0
  simpa using (h1.mul hq).div hp' one_ne_zero

private lemma fussCatalanGeneralC1_eq (p : ℕ) (hp : 2 ≤ p) :
    fussCatalanGeneralC1 p =
      -(1 / ((p - 1 : ℕ) : ℝ)) + fussCatalanGeneralStirlingC p := by
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hp))
  have hqR : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have hq : 0 < p - 1 := by omega
    exact_mod_cast Nat.ne_of_gt hq
  have hqcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  unfold fussCatalanGeneralC1 fussCatalanGeneralStirlingC
  field_simp [hpR, hqR]
  rw [hqcast]
  ring

private lemma fussCatalanGeneralC2_eq (p : ℕ) :
    fussCatalanGeneralC2 p =
      1 / (((p - 1 : ℕ) : ℝ) ^ 2) +
        (fussCatalanGeneralStirlingC p) ^ 2 / 2 +
          (-(1 / ((p - 1 : ℕ) : ℝ))) * fussCatalanGeneralStirlingC p := by
  unfold fussCatalanGeneralC2
  ring

private lemma fussCatalanRelativeCore_thirdOrder (p : ℕ) (hp : 2 ≤ p) :
    (fun n : ℕ =>
      rationalPrefactor (p - 1) n *
          (stirlingInvRatio n * stirlingInvRatio ((p - 1) * n) /
            stirlingInvRatio (p * n)) -
        fussCatalanGeneralThirdApprox p n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hq0 : 0 < p - 1 := by omega
  have hrat := rationalPrefactor_thirdOrder (p - 1) hq0
  have hstir := stirlingInvProduct_thirdOrder p hp
  have hstirO :
      (fun n : ℕ =>
        stirlingInvRatio n * stirlingInvRatio ((p - 1) * n) /
          stirlingInvRatio (p * n))
        =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    (stirlingInvProduct_tendsto_one p hp).isBigO_one ℝ
  have hratApproxO :
      (fun n : ℕ => rationalPrefactorApprox (p - 1) n)
        =O[atTop] fun _n : ℕ => (1 : ℝ) :=
    (rationalPrefactorApprox_tendsto_one (p - 1)).isBigO_one ℝ
  have hprod :=
    product_two_sub_product_two_isLittleO hrat hstir hstirO hratApproxO
  have hpolyRaw :=
    poly2_mul_trunc_isLittleO
      (-(1 / ((p - 1 : ℕ) : ℝ)))
      (1 / (((p - 1 : ℕ) : ℝ) ^ 2))
      (fussCatalanGeneralStirlingC p)
      ((fussCatalanGeneralStirlingC p) ^ 2 / 2)
  have hpoly :
      (fun n : ℕ =>
        rationalPrefactorApprox (p - 1) n * stirlingProductApprox p n -
          fussCatalanGeneralThirdApprox p n)
        =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
    refine hpolyRaw.congr_left ?_
    intro n
    unfold rationalPrefactorApprox stirlingProductApprox fussCatalanGeneralThirdApprox poly2
    rw [fussCatalanGeneralC1_eq p hp, fussCatalanGeneralC2_eq p]
    ring
  have htotal := hprod.add hpoly
  refine htotal.congr_left ?_
  intro n
  ring

private lemma factorial_eq_stirlingScale_div_invRatio {m : ℕ} (hm : m ≠ 0) :
    (((m.factorial : ℕ) : ℝ)) = stirlingScale m / stirlingInvRatio m := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hsqrtπ : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrt2m : Real.sqrt (2 * (m : ℝ)) ≠ 0 := by positivity
  have hpow : ((m : ℝ) / Real.exp 1) ^ m ≠ 0 := by
    exact pow_ne_zero _ (div_ne_zero hmR (Real.exp_ne_zero 1))
  have hsqrt_split :
      Real.sqrt (2 * (m : ℝ) * Real.pi) =
        Real.sqrt (2 * (m : ℝ)) * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * (m : ℝ))]
  unfold stirlingScale stirlingInvRatio Stirling.stirlingSeq
  rw [hsqrt_split]
  field_simp [hmR, hsqrtπ, hsqrt2m, hpow]

private lemma stirlingInvRatio_ne_zero_of_pos {m : ℕ} (hm : 0 < m) :
    stirlingInvRatio m ≠ 0 := by
  unfold stirlingInvRatio
  exact div_ne_zero (by positivity) (stirlingSeq_pos_of_pos hm).ne'

private lemma stirlingScale_ne_zero_of_pos {m : ℕ} (hm : 0 < m) :
    stirlingScale m ≠ 0 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  unfold stirlingScale
  exact mul_ne_zero (by positivity) (pow_ne_zero _ (div_ne_zero hmR.ne' (Real.exp_ne_zero 1)))

private lemma factorial_ratio_eq_chooseScale_mul_invRatios
    (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    (((((q + 1) * n).factorial : ℕ) : ℝ) /
        ((((n.factorial : ℕ) : ℝ) * ((((q * n).factorial : ℕ) : ℝ))))) =
      fussCatalanChooseScale (q + 1) n *
        (stirlingInvRatio n * stirlingInvRatio (q * n) /
          stirlingInvRatio ((q + 1) * n)) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num : 0 < 1) hq
  have hqnpos : 0 < q * n := Nat.mul_pos hqpos hnpos
  have hpnpos : 0 < (q + 1) * n := Nat.mul_pos (Nat.succ_pos q) hnpos
  have hAn : stirlingInvRatio n ≠ 0 := stirlingInvRatio_ne_zero_of_pos hnpos
  have hAq : stirlingInvRatio (q * n) ≠ 0 := stirlingInvRatio_ne_zero_of_pos hqnpos
  have hAp : stirlingInvRatio ((q + 1) * n) ≠ 0 :=
    stirlingInvRatio_ne_zero_of_pos hpnpos
  have hSn : stirlingScale n ≠ 0 := stirlingScale_ne_zero_of_pos hnpos
  have hSq : stirlingScale (q * n) ≠ 0 := stirlingScale_ne_zero_of_pos hqnpos
  have hSp : stirlingScale ((q + 1) * n) ≠ 0 := stirlingScale_ne_zero_of_pos hpnpos
  rw [factorial_eq_stirlingScale_div_invRatio (m := (q + 1) * n)
        (Nat.ne_of_gt hpnpos),
    factorial_eq_stirlingScale_div_invRatio (m := n) hn,
    factorial_eq_stirlingScale_div_invRatio (m := q * n) (Nat.ne_of_gt hqnpos)]
  rw [show
      (stirlingScale ((q + 1) * n) / stirlingInvRatio ((q + 1) * n)) /
          ((stirlingScale n / stirlingInvRatio n) *
            (stirlingScale (q * n) / stirlingInvRatio (q * n))) =
        (stirlingScale ((q + 1) * n) / (stirlingScale n * stirlingScale (q * n))) *
          (stirlingInvRatio n * stirlingInvRatio (q * n) /
            stirlingInvRatio ((q + 1) * n)) by
        field_simp [hAn, hAq, hAp, hSn, hSq, hSp]
        ]
  rw [stirling_choose_scale_succ_eq q n hq hn]

private lemma fussCatalanChooseScale_ne_zero_succ
    (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    fussCatalanChooseScale (q + 1) n ≠ 0 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold fussCatalanChooseScale fussCatalanBase
  simp only [Nat.add_sub_cancel]
  positivity

private lemma fussCatalan_succ_ratio_eq_core
    (q n : ℕ) (hq : 1 ≤ q) (hn : n ≠ 0) :
    (fussCatalan (q + 1) n : ℝ) / fussCatalanGeneralMainTermBase (q + 1) n =
      rationalPrefactor q n *
        (stirlingInvRatio n * stirlingInvRatio (q * n) /
          stirlingInvRatio ((q + 1) * n)) := by
  have hp : 2 ≤ q + 1 := by omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num : 0 < 1) hq
  have hqnpos : 0 < q * n := Nat.mul_pos hqpos hnpos
  have hpnpos : 0 < (q + 1) * n := Nat.mul_pos (Nat.succ_pos q) hnpos
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hqpos
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hqn1 : (((q * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hscale : fussCatalanChooseScale (q + 1) n ≠ 0 :=
    fussCatalanChooseScale_ne_zero_succ q n hq hn
  have hAp : stirlingInvRatio ((q + 1) * n) ≠ 0 :=
    stirlingInvRatio_ne_zero_of_pos hpnpos
  have hmain :
      fussCatalanGeneralMainTermBase (q + 1) n =
        fussCatalanChooseScale (q + 1) n / ((q : ℝ) * (n : ℝ)) := by
    symm
    simpa [fussCatalanGeneralMainTermBase, fussCatalanGeneralLeadingConstant] using
      fussCatalan_scale_succ_simplified q n hq hn
  rw [fussCatalan_cast (q + 1) n hp, choose_succ_mul_cast q n,
    factorial_ratio_eq_chooseScale_mul_invRatios q n hq hn, hmain]
  unfold rationalPrefactor
  norm_num [Nat.cast_mul, Nat.cast_add]
  field_simp [hqR, hnR, hqn1, hscale, hAp]

private theorem fussCatalanGeneral_relative_thirdOrder_base (p : ℕ) (hp : 2 ≤ p) :
    (fun n : ℕ =>
      (fussCatalan p n : ℝ) / fussCatalanGeneralMainTermBase p n -
        fussCatalanGeneralThirdApprox p n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  have hcore := fussCatalanRelativeCore_thirdOrder p hp
  refine hcore.congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hq : 1 ≤ p - 1 := by omega
  have hpq : p - 1 + 1 = p := by omega
  have hbridge := fussCatalan_succ_ratio_eq_core (p - 1) n hq (Nat.ne_of_gt hn)
  simpa [hpq] using
    (congrArg (fun x : ℝ => x - fussCatalanGeneralThirdApprox p n) hbridge).symm

private lemma fussCatalanGeneral_rho_inv_eq_base (p : ℕ) (hp : 2 ≤ p) :
    (fussCatalanGeneralRho p)⁻¹ = fussCatalanBase p := by
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2) hp))
  have hqR : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
    have hq : 0 < p - 1 := by omega
    exact_mod_cast Nat.ne_of_gt hq
  have hpPow : (p : ℝ) ^ p ≠ 0 := pow_ne_zero _ hpR
  have hqPow : ((p - 1 : ℕ) : ℝ) ^ (p - 1) ≠ 0 := pow_ne_zero _ hqR
  unfold fussCatalanGeneralRho fussCatalanBase
  field_simp [hpPow, hqPow]

private lemma fussCatalanGeneral_rho_rpow_neg_nat_eq_base_pow
    (p n : ℕ) (hp : 2 ≤ p) :
    (fussCatalanGeneralRho p) ^ (-(n : ℝ)) = fussCatalanBase p ^ n := by
  have hρpos : 0 < fussCatalanGeneralRho p := by
    have hpR : 0 < (p : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hp)
    have hqR : 0 < ((p - 1 : ℕ) : ℝ) := by
      have hq : 0 < p - 1 := by omega
      exact_mod_cast hq
    unfold fussCatalanGeneralRho
    positivity
  rw [Real.rpow_neg hρpos.le, Real.rpow_natCast, ← inv_pow,
    fussCatalanGeneral_rho_inv_eq_base p hp]

private lemma fussCatalanGeneralMainTerm_eq_base (p n : ℕ) (hp : 2 ≤ p) :
    fussCatalanGeneralMainTerm p n = fussCatalanGeneralMainTermBase p n := by
  unfold fussCatalanGeneralMainTerm fussCatalanGeneralMainTermBase
  rw [fussCatalanGeneral_rho_rpow_neg_nat_eq_base_pow p n hp]
  ring

private theorem fussCatalanGeneral_relative_thirdOrder_fussCatalan (p : ℕ) (hp : 2 ≤ p) :
    (fun n : ℕ =>
      (fussCatalan p n : ℝ) / fussCatalanGeneralMainTerm p n -
        fussCatalanGeneralThirdApprox p n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine (fussCatalanGeneral_relative_thirdOrder_base p hp).congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards with n
  rw [fussCatalanGeneralMainTerm_eq_base p n hp]

private lemma fussCatalanRaneyCoeff_eq_fussCatalan
    (p n : ℕ) (hp : 2 ≤ p) :
    fussCatalanRaneyCoeff p n = (fussCatalan p n : ℝ) := by
  have hden : ((((p - 1) * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [fussCatalan_cast p n hp]
  unfold fussCatalanRaneyCoeff
  field_simp [hden]

end
end AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanNS

open AnalyticCombinatorics AnalyticCombinatorics.Ch7 AnalyticCombinatorics.Ch7.SingularityApp AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanNS
set_option maxHeartbeats 1600000
open Filter Asymptotics
open scoped Topology
theorem solution (p : ℕ) (hp : 2 ≤ p) :
    (fun n : ℕ =>
      fussCatalanRaneyCoeff p n / fussCatalanGeneralMainTerm p n -
        fussCatalanGeneralThirdApprox p n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by
  refine (fussCatalanGeneral_relative_thirdOrder_fussCatalan p hp).congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards with n
  rw [fussCatalanRaneyCoeff_eq_fussCatalan p n hp]
