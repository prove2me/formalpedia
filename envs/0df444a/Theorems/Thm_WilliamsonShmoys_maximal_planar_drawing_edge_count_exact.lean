-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_exact
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_exact
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:39:37.621488+00:00
-- url     : https://prove2.me/theorems/8742a5e4-f287-4b84-b71a-f78e094dd85c
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite vertices that has no strictly larger drawable supergraph has exactly three times its number of vertices minus six edges. The proof reduces to connectedness and triangular faces for maximal planar drawings, followed by Euler counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_exact
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hMax : ∀ K : SimpleGraph V,
      J ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K = J) :
    J.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
