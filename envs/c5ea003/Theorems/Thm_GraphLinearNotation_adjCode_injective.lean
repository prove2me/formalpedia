-- Prove2me | Theorems.Thm_GraphLinearNotation_adjCode_injective
-- name    : GraphLinearNotation.adjCode_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:38:22.02974+00:00
-- url     : https://prove2.me/theorems/fce55dda-c0eb-4aa7-865e-4224eba38781
-- title:
--   The ordered adjacency-matrix bit code is injective.
-- statement:
--   The ordered adjacency-matrix bit code is injective.
--
--   ```lean
--   theorem GraphLinearNotation.adjCode_injective: Function.Injective (adjCode : SimpleGraph (Fin n) → ℕ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/GraphLinearNotation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/GraphLinearNotation.lean#L117

-- Thm stub generated from Probability/GraphLinearNotation.lean
import Mathlib
import Definitions.Def_Probability_GraphLinearNotation
/-
  Graph Linear Notation

  For finite simple graphs on `Fin n`, we formalize *graph linear notation* (`gln`)
  as the maximum binary adjacency code taken over all vertex relabelings
  (permutations of the vertex set), and prove that it is a complete invariant for
  graph isomorphism.

  Main results:
  * `adjCode_injective`     : the ordered adjacency-matrix bit code is injective.
  * `gln_attained`          : the maximum defining `gln` is attained by some relabeling.
  * `gln_iso_invariant`     : isomorphic graphs have equal `gln`.
  * `gln_complete`          : equal `gln` implies isomorphism.
  * `gln_eq_iff_iso`        : `gln G = gln H ↔ IsGraphIso G H`.
-/

open Finset

open GraphLinearNotation

variable {n : ℕ}










/-
A sum of distinct powers of two with `0/1` coefficients determines the coefficients:
if `∑ i, f i * 2 ^ e i = ∑ i, g i * 2 ^ e i` with `e` injective and `f i, g i ≤ 1`, then `f = g`.
-/

theorem GraphLinearNotation.adjCode_injective: Function.Injective (adjCode : SimpleGraph (Fin n) → ℕ) := by sorry
