-- Prove2me | Theorems.Thm_AdjacencyDegreeMomentBridge_adjMatrix_rowSum_eq_degree
-- name    : AdjacencyDegreeMomentBridge.adjMatrix_rowSum_eq_degree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:04:50.025988+00:00
-- url     : https://prove2.me/theorems/14fad81d-9c7e-409d-86ce-14aee667d6ad
-- title:
--   The adjacency matrix has row sum equal to the (real-valued) vertex degree.
-- statement:
--   The adjacency matrix has row sum equal to the (real-valued) vertex degree.
--
--   ```lean
--   theorem AdjacencyDegreeMomentBridge.adjMatrix_rowSum_eq_degree    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
--       rowSum (G.adjMatrix ℝ) v = (G.degree v : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/AdjacencyDegreeMomentBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/AdjacencyDegreeMomentBridge.lean#L71

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

theorem AdjacencyDegreeMomentBridge.adjMatrix_rowSum_eq_degree    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    rowSum (G.adjMatrix ℝ) v = (G.degree v : ℝ) := by sorry
