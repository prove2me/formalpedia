-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_for_maximal_drawing_32fad0ec
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_for_maximal_drawing_32fad0ec
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:00:28.527842+00:00
-- url     : https://prove2.me/theorems/1c8eeea2-347b-4fb9-8029-72229f48f1dc
-- title:
--   Edge lower bound for an edge maximal planar drawing
-- statement:
--   An edge maximal graph with the specified planar drawing and at least three vertices has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_for_maximal_drawing_32fad0ec
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
