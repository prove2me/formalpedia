-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_for_maximal_exact_count
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_for_maximal_exact_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:36:05.421763+00:00
-- url     : https://prove2.me/theorems/89691b72-2847-4893-8243-989bffe1ec97
-- title:
--   Euler edge bound for a planar drawing
-- statement:
--   A graph with the specified crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the Euler face-incidence upper bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_for_maximal_exact_count
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    J.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
