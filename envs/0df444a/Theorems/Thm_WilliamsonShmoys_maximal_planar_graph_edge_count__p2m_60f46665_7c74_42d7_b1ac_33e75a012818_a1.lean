-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_60f46665_7c74_42d7_b1ac_33e75a012818_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_60f46665_7c74_42d7_b1ac_33e75a012818_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:13:01.597206+00:00
-- url     : https://prove2.me/theorems/92179202-75fd-4ebd-82a2-e854a66d92bd
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An edge maximal drawable finite simple graph with at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_60f46665_7c74_42d7_b1ac_33e75a012818_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M → M.edgeSet = L.edgeSet) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
