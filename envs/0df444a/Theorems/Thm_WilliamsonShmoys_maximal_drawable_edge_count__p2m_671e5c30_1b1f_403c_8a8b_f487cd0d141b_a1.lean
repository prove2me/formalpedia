-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:20:22.182192+00:00
-- url     : https://prove2.me/theorems/36d62909-fefb-443f-ad8e-654ce0b0b7dd
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal under drawable edge supergraphs has exactly three times its vertex count minus six edges. The lower bound includes the three-vertex case, where maximality forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count__p2m_671e5c30_1b1f_403c_8a8b_f487cd0d141b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
