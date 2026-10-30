-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_edge_bound
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:43:56.363666+00:00
-- url     : https://prove2.me/theorems/e3d40089-9b59-4dfa-90d1-30387e0795bb
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An edge-maximal drawable finite simple graph with at least three vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
