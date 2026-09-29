-- Prove2me | Theorems.Thm_NeuralHodgeDecisionSurfaces_square_cycle_classification
-- name    : NeuralHodgeDecisionSurfaces.square_cycle_classification
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:44:59.293333+00:00
-- url     : https://prove2.me/theorems/7b9fd431-9cc0-4675-90ad-937bbb6c8575
-- title:
--   Square cycle classification.
-- statement:
--   **Square cycle classification.** Every rational cycle on the square is a
--   unique scalar multiple of the sum of its four oriented linear edges.
--
--   ```lean
--   theorem NeuralHodgeDecisionSurfaces.square_cycle_classification(x : SquareChain) :
--       IsSquareCycle x ↔ ∃! a : ℚ, x = a • fundamentalSquareCycle := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NeuralHodgeDecisionSurfaces.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NeuralHodgeDecisionSurfaces.lean#L59

-- Thm stub generated from MachineLearning/NeuralHodgeDecisionSurfaces.lean
import Mathlib
import Definitions.Def_MachineLearning_NeuralHodgeDecisionSurfaces
/-
# A finite polyhedral Hodge shadow for ReLU decision surfaces

This file proves two concrete results that remain valid without imposing a
(nonexistent, in general) complex Hodge structure on a real ReLU decision set.

First, the cycle space of the four-edge square is exactly one-dimensional:
every rational 1-cycle is a common multiple of the sum of its four linear
edges.  Thus every class in this small polyhedral model has an explicit
face-supported representative.

Second, we study the proposed architecture-dependent numerical expression
`choose first p * choose last q * product interior`.  We prove its vanishing
range, reversal symmetry, and a uniform exponential estimate.
-/


open scoped BigOperators
open Finset

open NeuralHodgeDecisionSurfaces

/-! ## The square as a finite decision-surface model -/

theorem NeuralHodgeDecisionSurfaces.square_cycle_classification(x : SquareChain) :
    IsSquareCycle x ↔ ∃! a : ℚ, x = a • fundamentalSquareCycle := by sorry
