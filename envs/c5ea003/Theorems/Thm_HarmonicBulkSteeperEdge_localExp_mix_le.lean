-- Prove2me | Theorems.Thm_HarmonicBulkSteeperEdge_localExp_mix_le
-- name    : HarmonicBulkSteeperEdge.localExp_mix_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:44:40.261264+00:00
-- url     : https://prove2.me/theorems/3a077039-09c4-4ed2-b0d1-2a9594c71de0
-- title:
--   Quantitative edge excess.
-- statement:
--   **Quantitative edge excess.**  The local exponent of a bulk × edge mixture exceeds the
--   bulk exponent `a`, by at most `(w/(1-w)) * (b-a) * k^{-(b-a)}`.
--
--   ```lean
--   theorem HarmonicBulkSteeperEdge.localExp_mix_le{w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hab : a < b) {k : ℕ}
--       (hk : 1 ≤ k) :
--       localExp (mix w a b) k ≤ a + (w / (1 - w)) * (b - a) * (k : ℝ) ^ (-(b - a)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HarmonicBulkSteeperEdge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HarmonicBulkSteeperEdge.lean#L430

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

theorem HarmonicBulkSteeperEdge.localExp_mix_le{w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hab : a < b) {k : ℕ}
    (hk : 1 ≤ k) :
    localExp (mix w a b) k ≤ a + (w / (1 - w)) * (b - a) * (k : ℝ) ^ (-(b - a)) := by sorry
