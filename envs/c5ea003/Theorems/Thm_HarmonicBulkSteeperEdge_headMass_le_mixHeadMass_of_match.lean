-- Prove2me | Theorems.Thm_HarmonicBulkSteeperEdge_headMass_le_mixHeadMass_of_match
-- name    : HarmonicBulkSteeperEdge.headMass_le_mixHeadMass_of_match
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:44:10.583848+00:00
-- url     : https://prove2.me/theorems/40db32fe-3e01-4ac2-872c-6774f808a6fe
-- title:
--   Single-crossing window law.
-- statement:
--   **Single-crossing window law.**  If a pure power law with exponent `c` matches the head
--   mass of a bulk × edge mixture on the window `{1, …, m₂}`, then on every narrower window it
--   reports *less* head mass than the mixture.
--
--   ```lean
--   theorem HarmonicBulkSteeperEdge.headMass_le_mixHeadMass_of_match{w a b c : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
--       {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
--       (hmatch : headMass c n m₂ = mixHeadMass w a b n m₂) :
--       headMass c n m₁ ≤ mixHeadMass w a b n m₁ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HarmonicBulkSteeperEdge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HarmonicBulkSteeperEdge.lean#L686

-- Thm stub generated from Probability/HarmonicBulkSteeperEdge.lean
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

theorem HarmonicBulkSteeperEdge.headMass_le_mixHeadMass_of_match{w a b c : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    {m₁ m₂ n : ℕ} (hm₁ : 1 ≤ m₁) (h₁₂ : m₁ < m₂) (h₂n : m₂ < n)
    (hmatch : headMass c n m₂ = mixHeadMass w a b n m₂) :
    headMass c n m₁ ≤ mixHeadMass w a b n m₁ := by sorry
