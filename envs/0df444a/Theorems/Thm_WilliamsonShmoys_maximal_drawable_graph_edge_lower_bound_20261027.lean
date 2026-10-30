-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_20261027
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:14:26.588487+00:00
-- url     : https://prove2.me/theorems/3ef8bf35-336f-4caf-ba99-e80051587d3d
-- title:
--   Maximal drawable graph has at least 3n − 6 edges
-- statement:
--   A drawable finite simple graph on at least three vertices that is maximal among drawable graphs on the same vertex type has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by sorry
