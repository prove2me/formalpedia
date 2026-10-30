-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_retry_646b0e38
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_retry_646b0e38
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:17:42.267396+00:00
-- url     : https://prove2.me/theorems/542f205e-6d4b-4b80-a2d1-f3a946495b5f
-- title:
--   Maximal planar graph edge lower bound
-- statement:
--   An inclusion-maximal finite simple graph with the supplied crossing-free drawing and at least three vertices has at least 3|V|−6 edges. A proof route uses maximality to show no face permits inserting an edge, then combines Euler’s formula with edge-face incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_retry_646b0e38
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N → WilliamsonShmoys.HasPlanarDrawingOn N → N <= M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
