-- Prove2me | Theorems.Thm_NeuralHodgeDecisionSurfaces_architectureBound_pos_iff
-- name    : NeuralHodgeDecisionSurfaces.architectureBound_pos_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:44:48.278274+00:00
-- url     : https://prove2.me/theorems/0c8a9ae3-c20e-4a95-bbaf-c46a0c9fcd13
-- title:
--   If every intervening layer is nonzero, the architecture expression is
-- statement:
--   If every intervening layer is nonzero, the architecture expression is
--   positive exactly in the binomial support rectangle.
--
--   ```lean
--   theorem NeuralHodgeDecisionSurfaces.architectureBound_pos_iff    {first last p q : ℕ} {interior : List ℕ}
--       (hinterior : ∀ w ∈ interior, 0 < w) :
--       0 < architectureBound first last interior p q ↔
--         p ≤ first ∧ q ≤ last := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/NeuralHodgeDecisionSurfaces.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/NeuralHodgeDecisionSurfaces.lean#L147

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










/-! ## The proposed architecture expression -/

theorem NeuralHodgeDecisionSurfaces.architectureBound_pos_iff    {first last p q : ℕ} {interior : List ℕ}
    (hinterior : ∀ w ∈ interior, 0 < w) :
    0 < architectureBound first last interior p q ↔
      p ≤ first ∧ q ≤ last := by sorry
