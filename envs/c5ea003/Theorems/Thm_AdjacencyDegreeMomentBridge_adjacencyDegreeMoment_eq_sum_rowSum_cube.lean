-- Prove2me | Theorems.Thm_AdjacencyDegreeMomentBridge_adjacencyDegreeMoment_eq_sum_rowSum_cube
-- name    : AdjacencyDegreeMomentBridge.adjacencyDegreeMoment_eq_sum_rowSum_cube
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:03:37.698448+00:00
-- url     : https://prove2.me/theorems/7dafe3f8-7df2-45b0-b37c-a28c09ca7776
-- title:
--   Matrix/statistics connector.
-- statement:
--   **Matrix/statistics connector.** For every finite symmetric real matrix, the
--   adjacency-degree word `A D A`, tested against the all-ones vector on both sides,
--   is exactly the third raw moment of its row-sum vector.
--
--   ```lean
--   theorem AdjacencyDegreeMomentBridge.adjacencyDegreeMoment_eq_sum_rowSum_cube[DecidableEq V]
--       (A : Matrix V V ℝ) (hA : A.IsSymm) :
--       adjacencyDegreeMoment A = ∑ i, (rowSum A i) ^ 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/AdjacencyDegreeMomentBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/AdjacencyDegreeMomentBridge.lean#L34

-- Thm stub generated from Bridges/GraphTheory/AdjacencyDegreeMomentBridge.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_AdjacencyDegreeMomentBridge
/-
# Adjacency–degree moments and degree-distribution moments

This file formalizes a concrete connector suggested by adjacency-degree algebras.
For a symmetric matrix `A`, let `d` be its row-sum vector and `D = diag d`.
Then the scalar adjacency-degree moment

  1ᵀ A D A 1

is the third raw moment `∑ᵥ d(v)^3` of the row-sum distribution.  For a simple
undirected graph, `A` is the adjacency matrix and `d(v)` is the degree, so this
also counts homomorphisms from the three-leaf star: choose the image of its
center and then independently choose the images of its three leaves.

Thus one scalar word in the noncommutative adjacency-degree algebra connects
linear algebra, degree statistics, and graph homomorphism counting.
-/

open Matrix Finset
open scoped BigOperators

open AdjacencyDegreeMomentBridge

variable {V : Type*} [Fintype V]

theorem AdjacencyDegreeMomentBridge.adjacencyDegreeMoment_eq_sum_rowSum_cube[DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsSymm) :
    adjacencyDegreeMoment A = ∑ i, (rowSum A i) ^ 3 := by sorry
