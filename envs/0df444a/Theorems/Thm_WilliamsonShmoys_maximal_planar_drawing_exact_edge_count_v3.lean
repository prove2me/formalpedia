-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count_v3
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:02:27.167671+00:00
-- url     : https://prove2.me/theorems/8cf194c3-b653-43c1-98b1-0df16d8c12e1
-- title:
--   Edge count of a maximal finite planar drawing
-- statement:
--   A drawable graph on at least three finite vertices that has no proper drawable supergraph on the same vertex type has exactly `3|V|−6` edges. Maximality forces a triangulation; Euler’s formula and triangular face boundaries give the count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ H' : SimpleGraph V,
      H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
