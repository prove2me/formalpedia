-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_d5ec0378_40af_49f0_96a5_235e13fa397b_a3
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_d5ec0378_40af_49f0_96a5_235e13fa397b_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:04:56.503993+00:00
-- url     : https://prove2.me/theorems/09553c75-05d3-4866-a115-40c42a94c393
-- title:
--   Euler edge bound for a finite planar drawing
-- statement:
--   A finite simple graph on at least three vertices with an injective, crossing-free drawing as specified by `HasPlanarDrawingOn` has at most `3 * card V - 6` edges. This is the Euler edge bound and remains valid when the graph is disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_d5ec0378_40af_49f0_96a5_235e13fa397b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    U.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
