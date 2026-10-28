-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_euler_edge_count
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_has_euler_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:25:57.94989+00:00
-- url     : https://prove2.me/theorems/2ef74a34-fa40-4031-b5f2-5c9a50dcf66f
-- title:
--   An edge-maximal planar graph has the triangulation edge count
-- statement:
--   A graph on at least three vertices that has the specified planar drawing and is maximal among planar supergraphs on that same vertex type has exactly `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_has_euler_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
