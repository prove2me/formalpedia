-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_086e0035_b1b1_47b8_9347_227154b90d05_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_086e0035_b1b1_47b8_9347_227154b90d05_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:39:32.16471+00:00
-- url     : https://prove2.me/theorems/a656f539-9504-4e65-b2f9-35a6aea29cbf
-- title:
--   Exact edge count for a maximal planar drawing
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_086e0035_b1b1_47b8_9347_227154b90d05_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
