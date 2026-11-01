-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_3b70d152_dbfb_4f09_8d03_767be9da3cd3_a2
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_3b70d152_dbfb_4f09_8d03_767be9da3cd3_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:11:11.747196+00:00
-- url     : https://prove2.me/theorems/ba06bb4d-e92b-4537-887e-0721c652813c
-- title:
--   Euler edge bound for planar drawings
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges, whether or not it is connected. Prove this by applying Euler’s formula componentwise, with separate bounds for components of size one or two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_3b70d152_dbfb_4f09_8d03_767be9da3cd3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
