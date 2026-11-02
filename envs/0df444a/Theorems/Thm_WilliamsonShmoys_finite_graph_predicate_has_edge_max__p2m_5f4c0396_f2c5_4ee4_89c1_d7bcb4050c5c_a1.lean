-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_predicate_has_edge_max__p2m_5f4c0396_f2c5_4ee4_89c1_d7bcb4050c5c_a1
-- name    : WilliamsonShmoys.finite_graph_predicate_has_edge_max__p2m_5f4c0396_f2c5_4ee4_89c1_d7bcb4050c5c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:00:21.24577+00:00
-- url     : https://prove2.me/theorems/1e88f964-0e96-4350-89d1-f91ecb7f41a9
-- title:
--   Maximum edge count among finite graphs satisfying a predicate
-- statement:
--   For any finite vertex type and any inhabited predicate on its simple graphs, there is a graph satisfying the predicate whose finite edge count is at least that of every other graph satisfying it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_predicate_has_edge_max__p2m_5f4c0396_f2c5_4ee4_89c1_d7bcb4050c5c_a1
    {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (hP : ∃ G, P G) :
    letI : (G : SimpleGraph V) → DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V, P H ∧
      (∀ K : SimpleGraph V, P K → K.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
