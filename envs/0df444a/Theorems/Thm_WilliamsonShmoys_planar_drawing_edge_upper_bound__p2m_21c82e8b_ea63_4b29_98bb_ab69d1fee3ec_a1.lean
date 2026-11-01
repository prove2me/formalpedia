-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_21c82e8b_ea63_4b29_98bb_ab69d1fee3ec_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_21c82e8b_ea63_4b29_98bb_ab69d1fee3ec_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:35:46.384935+00:00
-- url     : https://prove2.me/theorems/9ece4b06-ebe0-4502-889a-c25beda9e246
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Any graph with the supplied planar drawing on at least three vertices has at most 3|V|−6 edges. This removes the upper-bound half of the target. The independent proof route is Euler’s formula with face-edge incidence counting, including the component adjustment for disconnected graphs. The strict size hypothesis is preserved because the usual bound requires at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_21c82e8b_ea63_4b29_98bb_ab69d1fee3ec_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
