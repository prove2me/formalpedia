-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_76f2d72e_f140_4cd7_bf10_fd0bb7e9203e_a2
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_76f2d72e_f140_4cd7_bf10_fd0bb7e9203e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:25:47.174565+00:00
-- url     : https://prove2.me/theorems/bd087b81-ae5f-45b5-8596-e80428b4743a
-- title:
--   Planar drawings obey the simple planar edge bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_76f2d72e_f140_4cd7_bf10_fd0bb7e9203e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
