-- Prove2me | solution 1 for HarmonicBulkSteeperEdge.harmonic_edge_mixture_matches_observed_peak_end
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:39:59.106825+00:00
-- url     : https://prove2.me/submissions/d8ddb15b-1a77-4ee6-b0f9-6ea1cb36a884

-- Sol generated from Probability/HarmonicBulkSteeperEdge.lean
import Mathlib
import Definitions.Def_Probability_HarmonicBulkSteeperEdge
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



lemma pw_one (a : ℝ) : pw a 1 = 1 := by
  simp [pw]




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
theorem solution:
    mix (54/127) 1 2 1 / mix (54/127) 1 2 2 = 2.54 := by
  have h1 : pw 1 1 = 1 := pw_one 1
  have h2 : pw 2 1 = 1 := pw_one 2
  have h3 : pw (1:ℝ) 2 = 1/2 := by
    have : ((2:ℕ) : ℝ) = (2:ℝ) := by norm_num
    rw [pw, this]
    rw [show (-(1:ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have h4 : pw (2:ℝ) 2 = 1/4 := by
    have : ((2:ℕ) : ℝ) = (2:ℝ) := by norm_num
    rw [pw, this]
    rw [show (-(2:ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  rw [mix, mix, h1, h2, h3, h4]
  norm_num
