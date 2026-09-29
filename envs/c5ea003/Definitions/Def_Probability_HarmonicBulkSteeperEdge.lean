-- Prove2me | Definitions.Def_Probability_HarmonicBulkSteeperEdge
-- name    : Probability_HarmonicBulkSteeperEdge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:18.079314+00:00
-- url     : https://prove2.me/theorems/69e134ca-ab9a-4046-b535-1380f63d8645
-- title:
--   Aether Catalog definitions — Probability_HarmonicBulkSteeperEdge
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.HarmonicBulkSteeperEdge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/HarmonicBulkSteeperEdge.lean by skeleton subtraction
import Mathlib
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

namespace HarmonicBulkSteeperEdge

/-! ## The discrete power-law kernel -/

/-- Unnormalised power-law weight `k ↦ k^(-a)`; `a = 1` is the harmonic kernel. -/
noncomputable def pw (a : ℝ) (k : ℕ) : ℝ := (k : ℝ) ^ (-a)






/-! ## Head masses and first-order stochastic dominance -/

/-- Total weight of the head window `{1, …, m}`. -/
noncomputable def headSum (a : ℝ) (m : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 m, pw a k

/-- Fraction of the total weight on `{1, …, n}` carried by the head window `{1, …, m}`. -/
noncomputable def headMass (a : ℝ) (n m : ℕ) : ℝ := headSum a m / headSum a n










/-! ## Mediants -/


/-! ## Two-component (bulk × edge) kernels -/

/-- Mixture of a bulk kernel with exponent `a` and an edge kernel with exponent `b`. -/
noncomputable def mix (w a b : ℝ) (k : ℕ) : ℝ := (1 - w) * pw a k + w * pw b k

/-- The share of the weight at index `k` carried by the steep (edge) component. -/
noncomputable def steepShare (w a b : ℝ) (k : ℕ) : ℝ := w * pw b k / mix w a b k

/-- Local exponent read off from two consecutive indices. -/
noncomputable def localExp (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  Real.log (f k / f (k + 1)) / Real.log ((k + 1 : ℝ) / k)






/-- Head mass of a mixture, over the window `{1, …, m}` inside `{1, …, n}`. -/
noncomputable def mixHeadSum (w a b : ℝ) (m : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 m, mix w a b k

noncomputable def mixHeadMass (w a b : ℝ) (n m : ℕ) : ℝ := mixHeadSum w a b m / mixHeadSum w a b n



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



/-- Ratio of the mixture to the pure power law with exponent `c`. -/
noncomputable def mixRatio (w a b c : ℝ) (k : ℕ) : ℝ := mix w a b k / pw c k








/-! ## Weighted versus equal-weight counting

Equal-weight counting is the degenerate exponent `a = 0`, for which the head statistic is
exactly `m/n`.  Any genuinely decaying weight is strictly head-biased, so head statistics
read off an equal-weight dial and a `1/ℓ`-weighted dial are never comparable. -/



/-! ## Saturation dichotomy for the head dial

As the truncation `n` grows, the head statistic either saturates at a positive limit or
collapses to `0`, according to whether the exponent exceeds the harmonic value `1`.  The
harmonic kernel itself sits exactly on the non-saturating side of the threshold. -/









end HarmonicBulkSteeperEdge


