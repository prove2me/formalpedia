-- Prove2me | Definitions.Def_Probability_PercolationSelfDuality
-- name    : Probability_PercolationSelfDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:49.980378+00:00
-- url     : https://prove2.me/theorems/a91acb82-fafb-4d6c-ad44-e3b066c67147
-- title:
--   Aether Catalog definitions — Probability_PercolationSelfDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PercolationSelfDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PercolationSelfDuality.lean by skeleton subtraction
import Mathlib

/-!
# Self-duality and exact finite percolation thresholds

This file isolates the general symmetry argument behind exact self-dual crossing
probabilities. A crossing function on the Bernoulli parameter interval is
self-dual when complementing the parameter complements its value. Self-duality
forces value `1/2` at the midpoint; strict monotonicity makes that midpoint the
unique fair parameter and determines the strict subcritical and supercritical
inequalities.

The final theorems give the corresponding event-level statement. Any measurable
event exchanged with its complement by a measure-preserving transformation of a
probability space has probability exactly `1/2`.
-/

open Set MeasureTheory

namespace PercolationSelfDuality

/-- A real-valued crossing function is self-dual on the Bernoulli parameter
interval when parameter complementation also complements its value. -/
def IsSelfDualOnUnit (crossing : ℝ → ℝ) : Prop :=
  ∀ p ∈ Set.Icc (0 : ℝ) 1, crossing (1 - p) = 1 - crossing p








end PercolationSelfDuality


