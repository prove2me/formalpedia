-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:43:26.886756+00:00
-- url     : https://prove2.me/theorems/44dff1e2-5719-47a8-9ed7-630e7dfea2be
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   Every finite simple graph with a planar drawing and at least three vertices has at most 3|V|−6 edges. The vertex-count boundary is necessary for this form of the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_upper__p2m_9c5c2913_8662_47f3_b676_c48b7de0b279_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
