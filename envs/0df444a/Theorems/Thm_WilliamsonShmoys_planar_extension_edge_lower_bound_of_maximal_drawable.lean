-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_edge_lower_bound_of_maximal_drawable
-- name    : WilliamsonShmoys.planar_extension_edge_lower_bound_of_maximal_drawable
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:22:00.386293+00:00
-- url     : https://prove2.me/theorems/e9650e8f-e865-48b3-bcdd-880fe4d8e2af
-- title:
--   Maximal drawable graphs meet the planar edge lower bound
-- statement:
--   A drawable graph on at least three vertices that has no strict drawable supergraph on the same vertex type has at least three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_edge_lower_bound_of_maximal_drawable
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ Z : SimpleGraph V, G ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Z ≤ G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by sorry
