-- Prove2me | solution 1 for ChannelContinuity.eventual_sqrt_bound_of_weak_testing
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-07T23:45:25.008836+00:00
-- url     : https://prove2.me/submissions/a0cfeea9-0669-4082-b45e-5bb68015b070

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_CRCD_ChannelContinuity_ThreePiece

section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/






/-!
# The first limit in the three-piece argument

This file proves the real-analysis passage from equation `threepiecebound` to
equation `contradiction` in the supplied manuscript.  The operator-theoretic
three-piece estimate is a hypothesis, not an axiom or a proved quantum fact.

An eventual bound `b n ≤ B < 1` replaces a limsup.  Continuity of real powers
at exponent one also covers zero bases, so no nonzero-error assumption is used.
-/

open Filter Topology

namespace ChannelContinuity





end ChannelContinuity

open ChannelContinuity

open ChannelContinuity in
/-- The weak testing bound supplies a fixed eventual square-root error below
one at every rate above the relative entropy. -/
theorem solution
    {E : ℕ → ℝ} {d r : ℝ} (hd : 0 ≤ d) (hdr : d < r)
    (hweak : ∀ n : ℕ, 0 < n → E n ≤ d / r + 1 / ((n : ℝ) * r)) :
    ∃ B : ℝ, 0 ≤ B ∧ B < 1 ∧ ∀ᶠ n in atTop, Real.sqrt (E n) ≤ B := by
  have hr : 0 < r := lt_of_le_of_lt hd hdr
  have hratio : d / r < 1 := (div_lt_one hr).2 hdr
  have hsqrt : Real.sqrt (d / r) < 1 := by
    have := Real.sq_sqrt (div_nonneg hd hr.le)
    have := Real.sqrt_nonneg (d / r)
    nlinarith
  obtain ⟨B, hB0, hB1⟩ := exists_between hsqrt
  refine ⟨B, (Real.sqrt_nonneg _).trans hB0.le, hB1, ?_⟩
  have hrem : Tendsto (fun n : ℕ => 1 / ((n : ℝ) * r)) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_div, mul_comm] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 / r))
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (d / r + 1 / ((n : ℝ) * r)))
      atTop (𝓝 (Real.sqrt (d / r))) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_const_nhds.add hrem)
  filter_upwards [hlim.eventually (gt_mem_nhds hB0), eventually_gt_atTop 0]
    with n hn hn0
  exact (Real.sqrt_le_sqrt (hweak n hn0)).trans hn.le

end
