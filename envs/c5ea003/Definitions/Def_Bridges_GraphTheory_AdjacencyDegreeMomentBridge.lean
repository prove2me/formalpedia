-- Prove2me | Definitions.Def_Bridges_GraphTheory_AdjacencyDegreeMomentBridge
-- name    : Bridges_GraphTheory_AdjacencyDegreeMomentBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:11.501099+00:00
-- url     : https://prove2.me/theorems/11d6e98d-e579-489e-ac25-d49506461cfe
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_AdjacencyDegreeMomentBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.AdjacencyDegreeMomentBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/AdjacencyDegreeMomentBridge.lean by skeleton subtraction
import Mathlib
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

namespace AdjacencyDegreeMomentBridge

variable {V : Type*} [Fintype V]

/-- The row-sum vector of a square matrix. -/
def rowSum (A : Matrix V V ℝ) : V → ℝ := fun i => ∑ j, A i j

/-- The scalar moment obtained by summing all coordinates of `A D A 1`, where
`D` is the diagonal matrix of row sums. -/
def adjacencyDegreeMoment [DecidableEq V] (A : Matrix V V ℝ) : ℝ :=
  ∑ i, ((A * Matrix.diagonal (rowSum A) * A) *ᵥ (fun _ => (1 : ℝ))) i






end AdjacencyDegreeMomentBridge


