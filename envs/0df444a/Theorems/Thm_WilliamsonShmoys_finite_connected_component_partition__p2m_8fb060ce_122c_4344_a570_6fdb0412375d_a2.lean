-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_connected_component_partition__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2
-- name    : WilliamsonShmoys.finite_connected_component_partition__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:51:23.423246+00:00
-- url     : https://prove2.me/theorems/43810500-1f43-4f26-9fb2-357a895d104d
-- title:
--   Finite connected-component partition with exact counts
-- statement:
--   Every finite simple graph admits a partition into nonempty vertex blocks whose induced graphs are connected. The blocks are pairwise disjoint, cover all vertices, and their sizes sum to the vertex count. Singleton and pair blocks satisfy the stated simple-graph edge bounds, and the induced edge counts sum to the original edge count. The statement handles the empty graph with the empty partition. A proof route is to use equivalence classes under graph reachability, then count vertices and edges by their unique component; simplicity gives the small-block bounds.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_connected_component_partition__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a2
    {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     ∃ C : Finset (Finset V),
      (∀ B ∈ C, 0 < B.card) ∧
      (∀ B₁ ∈ C, ∀ B₂ ∈ C, B₁ ≠ B₂ →
        Disjoint (↑B₁ : Set V) (↑B₂ : Set V)) ∧
      (∀ v : V, ∃ B ∈ C, v ∈ B) ∧
      Fintype.card V = ∑ B ∈ C, B.card ∧
      (∀ B ∈ C,
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).Connected) ∧
      (∀ B ∈ C, B.card = 1 →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).edgeFinset.card = 0) ∧
      (∀ B ∈ C, B.card = 2 →
        letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _
        (N.induce (↑B : Set V)).edgeFinset.card ≤ 1) ∧
      N.edgeFinset.card =
        ∑ B ∈ C,
          (letI : Fintype {v // v ∈ (↑B : Set V)} := Fintype.ofFinite _;
           (N.induce (↑B : Set V)).edgeFinset.card)) := by sorry
