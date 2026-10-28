-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_19f31498_c1c5_41a0_a186_562a063d6dde
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_19f31498_c1c5_41a0_a186_562a063d6dde
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:40:38.661191+00:00
-- url     : https://prove2.me/theorems/d8ec29ea-d4bc-4299-90ac-744ba97d01d4
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A finite simple graph on at least three vertices that admits a planar drawing and is maximal among planar-drawable supergraphs on its vertex set has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_19f31498_c1c5_41a0_a186_562a063d6dde
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J →
      J.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
