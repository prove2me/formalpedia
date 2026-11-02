-- Prove2me | Theorems.Thm_WilliamsonShmoys_graph_edge_completion__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
-- name    : WilliamsonShmoys.graph_edge_completion__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:18:36.510905+00:00
-- url     : https://prove2.me/theorems/c389a76b-40bd-4622-b7b4-86084fd49151
-- title:
--   Complete a graph to a prescribed feasible edge count
-- statement:
--   For a finite linearly ordered vertex type, if a graph has at most m edges and m does not exceed the number of possible unordered vertex pairs, then it has a supergraph on the same vertices with exactly m edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.graph_edge_completion__p2m_f3a63840_9387_418b_904c_fbe2e8408361_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (m : Nat) :
    letI : (G : SimpleGraph V) → DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    K.edgeFinset.card ≤ m →
    m ≤ Fintype.card V * (Fintype.card V - 1) / 2 →
    ∃ H : SimpleGraph V, K ≤ H ∧ H.edgeFinset.card = m := by sorry
