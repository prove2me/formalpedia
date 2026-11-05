-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_connected_extension_of_one_edge__p2m_aa9f8502_788d_4376_8cf6_48061960ef49_a2
-- name    : WilliamsonShmoys.finite_graph_connected_extension_of_one_edge__p2m_aa9f8502_788d_4376_8cf6_48061960ef49_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:49:27.458531+00:00
-- url     : https://prove2.me/theorems/9fc762a8-5f43-4315-941e-21ea4c59e3e4
-- title:
--   Finite graph extension by repeated cross-component edges
-- statement:
--   For any predicate on finite graphs, if each disconnected graph satisfying the predicate has an extension that adds one edge between unreachable vertices and preserves the predicate, then the original graph has a connected supergraph satisfying the predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_graph_connected_extension_of_one_edge__p2m_aa9f8502_788d_4376_8cf6_48061960ef49_a2
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (hP : P G)
    (hstep : ∀ G : SimpleGraph V,
      P G → ¬ G.Connected →
      ∃ u v : V, ¬ G.Reachable u v ∧
        ∃ H : SimpleGraph V,
          G ≤ H ∧
          H.edgeSet = G.edgeSet ∪ {Sym2.mk u v} ∧
          P H) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ P H := by sorry
