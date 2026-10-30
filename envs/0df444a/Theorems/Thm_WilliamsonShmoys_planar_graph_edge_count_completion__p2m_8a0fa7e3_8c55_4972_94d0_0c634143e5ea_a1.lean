-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_completion__p2m_8a0fa7e3_8c55_4972_94d0_0c634143e5ea_a1
-- name    : WilliamsonShmoys.planar_graph_edge_count_completion__p2m_8a0fa7e3_8c55_4972_94d0_0c634143e5ea_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T11:49:41.209583+00:00
-- url     : https://prove2.me/theorems/dc74ed81-22cf-4790-bfe4-28c52731184f
-- title:
--   Planar graphs admit a maximal edge-count completion on the same vertices
-- statement:
--   Every graph with a crossing-free drawing on at least three vertices can be extended, using only edges between the existing vertices, to a planar graph with exactly `3|V| - 6` edges. One route is to extend to a maximal planar embedding, establish that its faces are triangular, and use Euler's formula. The strict lower bound of three vertices is necessary for this edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_edge_count_completion__p2m_8a0fa7e3_8c55_4972_94d0_0c634143e5ea_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet ⊆ K.edgeSet ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
