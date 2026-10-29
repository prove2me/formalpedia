-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_bound__p2m_1016eb9f_955e_4666_8793_89a9a11ff9b9_a5
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_bound__p2m_1016eb9f_955e_4666_8793_89a9a11ff9b9_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T01:52:09.277994+00:00
-- url     : https://prove2.me/theorems/72b0aa52-bf32-4c2a-812c-1918a1fafd7b
-- title:
--   Edge bound for a maximal drawable graph
-- statement:
--   Every drawable simple graph maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_bound__p2m_1016eb9f_955e_4666_8793_89a9a11ff9b9_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L <= M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M <= L) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by sorry
