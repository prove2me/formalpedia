-- Prove2me | Theorems.Thm_HarmonicBulkSteeperEdge_headMass_mix_mem_Ioo
-- name    : HarmonicBulkSteeperEdge.headMass_mix_mem_Ioo
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:43:40.331925+00:00
-- url     : https://prove2.me/theorems/4bfde850-0760-4fa7-9bd7-9ac90dc255d1
-- title:
--   The head mass of a bulk × edge mixture is a strict mediant of the two pure head
-- statement:
--   **The head mass of a bulk × edge mixture is a strict mediant** of the two pure head
--   masses: the mixture is edge-enriched relative to the bulk, but never as much as the pure
--   edge kernel.
--
--   ```lean
--   theorem HarmonicBulkSteeperEdge.headMass_mix_mem_Ioo{w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hab : a < b) {m n : ℕ}
--       (hm : 1 ≤ m) (hmn : m < n) :
--       headMass a n m < mixHeadMass w a b n m ∧ mixHeadMass w a b n m < headMass b n m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HarmonicBulkSteeperEdge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HarmonicBulkSteeperEdge.lean#L279

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

theorem HarmonicBulkSteeperEdge.headMass_mix_mem_Ioo{w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (hab : a < b) {m n : ℕ}
    (hm : 1 ≤ m) (hmn : m < n) :
    headMass a n m < mixHeadMass w a b n m ∧ mixHeadMass w a b n m < headMass b n m := by sorry
