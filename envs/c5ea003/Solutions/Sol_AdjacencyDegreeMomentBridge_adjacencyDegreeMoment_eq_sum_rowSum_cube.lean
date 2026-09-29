-- Prove2me | solution 1 for AdjacencyDegreeMomentBridge.adjacencyDegreeMoment_eq_sum_rowSum_cube
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:39:25.361125+00:00
-- url     : https://prove2.me/submissions/86dd3b53-8cb1-40cd-899a-948f464b9441

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
theorem solution[DecidableEq V]
    (A : Matrix V V ℝ) (hA : A.IsSymm) :
    adjacencyDegreeMoment A = ∑ i, (rowSum A i) ^ 3 := by
  have hones : A *ᵥ (fun _ => (1 : ℝ)) = rowSum A := by
    funext i
    simp [Matrix.mulVec, dotProduct, rowSum]
  have hdiag : Matrix.diagonal (rowSum A) *ᵥ rowSum A =
      fun i => (rowSum A i) ^ 2 := by
    funext i
    rw [Matrix.mulVec_diagonal]
    ring
  unfold adjacencyDegreeMoment
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hones, hdiag]
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ i, ∑ j, A i j * rowSum A j ^ 2) =
        ∑ j, (∑ i, A i j) * rowSum A j ^ 2 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.sum_mul]
    _ = ∑ j, rowSum A j * rowSum A j ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          unfold rowSum
          apply Finset.sum_congr rfl
          intro i _
          exact hA.apply j i
    _ = ∑ i, rowSum A i ^ 3 := by
          apply Finset.sum_congr rfl
          intro i _
          ring
