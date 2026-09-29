-- Prove2me | solution 1 for AdjacencyDegreeMomentBridge.adjMatrix_rowSum_eq_degree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:39:24.762214+00:00
-- url     : https://prove2.me/submissions/2635c5ab-8b30-4744-bb7f-8ca6c2290a1a

-- Sol generated from Bridges/GraphTheory/AdjacencyDegreeMomentBridge.lean
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









open AdjacencyDegreeMomentBridge in
theorem solution    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    rowSum (G.adjMatrix ℝ) v = (G.degree v : ℝ) := by
  unfold rowSum
  rw [show G.degree v = (G.neighborFinset v).card from rfl]
  calc
    (∑ j, G.adjMatrix ℝ v j) = ∑ j ∈ G.neighborFinset v, (1 : ℝ) := by
      rw [← Finset.sum_subset (s₁ := G.neighborFinset v) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro j hj
        simp only [SimpleGraph.mem_neighborFinset] at hj
        simp [SimpleGraph.adjMatrix_apply, hj]
      · exact Finset.subset_univ _
      · intro j _ hj
        simp only [SimpleGraph.mem_neighborFinset] at hj
        simp [SimpleGraph.adjMatrix_apply, hj]
    _ = (G.neighborFinset v).card := by simp
