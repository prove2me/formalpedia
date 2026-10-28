-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_retry_646b0e38
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_retry_646b0e38
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:32:43.755592+00:00
-- url     : https://prove2.me/theorems/82d3f981-edc6-4261-adff-4cb68e598032
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly three times its vertex count minus six edges. The proof route is to establish from the given drawing predicate that maximality forces a connected triangulation, then use Euler’s formula and count edge-face incidences. At three vertices the maximal graph is the triangle, which gives the boundary equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_retry_646b0e38
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
