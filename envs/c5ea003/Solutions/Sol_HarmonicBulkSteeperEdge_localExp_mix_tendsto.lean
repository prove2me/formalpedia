-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.localExp_mix_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:49:25.807768+00:00
-- url     : https://prove2.me/submissions/a2d79ac2-45dd-45f8-9bde-036da9f72f24

-- Sol generated from Probability/HarmonicBulkSteeperEdge.lean
import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
import Theorems.Thm_HarmonicBulkSteeperEdge_localExp_mix_le
import Theorems.Thm_HarmonicBulkSteeperEdge_localExp_mix_mem_Ioo
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Harmonic bulk × steeper edge: rigidity and mixture resolution for discrete power-law kernels

This file formalises the "harmonic bulk × steeper-edge kernel" refinement question:
a fitted bulk exponent (near the harmonic value `a = 1`, empirically `1.104`) coexists
with head statistics (edge fraction, first-decile mass, peak/end ratio) that each imply a
*steeper* exponent.  The mathematical content developed here is:

* **MLR ⇒ FOSD for the discrete power-law family.**  For weights `k ↦ k^(-a)` on
  `{1, …, n}`, a larger exponent puts more mass on every head window
  (`headMass_le_of_exponent_le`), strictly so (`headMass_lt_of_exponent_lt`).
* **Rigidity / identifiability.**  A single head statistic determines the exponent
  uniquely (`exponent_unique_of_headMass_eq`); hence two head windows reporting
  *different* implied exponents cannot be reconciled by any single power law
  (`no_single_exponent_fits_two_windows`).  This is the exact logical shape of the
  recorded tension.
* **Two-component resolution.**  For a mixture of a flat (bulk) and a steep (edge)
  component, every local exponent lies strictly between the two component exponents
  (`localExp_mix_mem_Ioo`), the head mass is a strict mediant
  (`headMass_mix_mem_Ioo`), and the steep component's local share is strictly
  decreasing in the index (`steepShare_strictAnti`) with limit `0`
  (`steepShare_tendsto_zero`).  So the steep component is *exactly* an edge phenomenon
  while the bulk is governed by the flat exponent.
* **A quantitative instance of the tension and its resolution.**  No power law with
  exponent `≤ 1.104` can produce the recorded peak/end ratio `2.54`
  (`pure_power_law_peak_end_lt_observed`), while the explicit harmonic-bulk /
  quadratic-edge mixture with weight `w = 54/127` produces it exactly
  (`harmonic_edge_mixture_matches_observed_peak_end`).
-/


open Finset Filter

open HarmonicBulkSteeperEdge

/-! ## The discrete power-law kernel -/







/-! ## Head masses and first-order stochastic dominance -/












/-! ## Mediants -/


/-! ## Two-component (bulk × edge) kernels -/













/-! ## The steep component is an edge phenomenon -/




/-! ## A quantitative instance: harmonic bulk versus the recorded peak/end ratio -/






/-! ## Quantitative bulk recovery for the local exponent

The local exponent of a bulk × edge mixture exceeds the bulk exponent at every index, but
only by `O(k^{-(b-a)})`: the edge steepening is a genuinely local excess that decays at a
power rate, and the measured exponent converges to the bulk exponent. -/





/-! ## Well-posedness of the window-implied exponent

A head statistic is turned into an *implied exponent* by inverting `a ↦ headMass a n m`.
The map is continuous and strictly increasing, so the inversion is well posed, and the
implied exponent of a bulk × edge mixture always lies strictly between the two component
exponents — the formal content of "a steeper edge inflates the exponent read off from a
head window". -/







/-! ## Single crossing: narrower windows report steeper exponents

The ratio of a two-component kernel to a pure power law is `U`-shaped in `log k` (a sum of
two exponentials, hence quasiconvex), so it can cross any level at most once from below.
This forces the *window-implied exponent* of a bulk × edge mixture to be antitone in the
window width: narrow head windows report steeper exponents than wide ones — precisely the
"steeper-than-harmonic left edge versus harmonic bulk" signature. -/











/-! ## Weighted versus equal-weight counting

Equal-weight counting is the degenerate exponent `a = 0`, for which the head statistic is
exactly `m/n`.  Any genuinely decaying weight is strictly head-biased, so head statistics
read off an equal-weight dial and a `1/ℓ`-weighted dial are never comparable. -/



/-! ## Saturation dichotomy for the head dial

As the truncation `n` grows, the head statistic either saturates at a positive limit or
collapses to `0`, according to whether the exponent exceeds the harmonic value `1`.  The
harmonic kernel itself sits exactly on the non-saturating side of the threshold. -/










open HarmonicBulkSteeperEdge in
theorem solution{w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hab : a < b) :
    Tendsto (fun k : ℕ => localExp (mix w a b) k) atTop (nhds a) := by
  have hpow : Tendsto (fun k : ℕ => (k : ℝ) ^ (-(b - a))) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (b - a)) atTop atTop :=
      tendsto_rpow_atTop (by linarith)
    have h2 : Tendsto (fun k : ℕ => ((k : ℝ)) ^ (b - a)) atTop atTop :=
      h1.comp tendsto_natCast_atTop_atTop
    have h3 : Tendsto (fun k : ℕ => ((k : ℝ) ^ (b - a))⁻¹) atTop (nhds 0) := h2.inv_tendsto_atTop
    refine h3.congr ?_
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [Real.zero_rpow (by linarith : b - a ≠ 0),
        Real.zero_rpow (by linarith : a - b ≠ 0)]
    · have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
      rw [Real.rpow_neg hk0.le]
  have hupper : Tendsto
      (fun k : ℕ => a + (w / (1 - w)) * (b - a) * (k : ℝ) ^ (-(b - a))) atTop (nhds a) := by
    have := (hpow.const_mul ((w / (1 - w)) * (b - a))).const_add a
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk
    exact (localExp_mix_mem_Ioo hw0 hw1 hab hk).1.le
  · filter_upwards [eventually_ge_atTop 1] with k hk
    exact localExp_mix_le hw0 hw1 hab hk
