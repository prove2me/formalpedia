-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:33:12.013726+00:00
-- url     : https://prove2.me/theorems/c4d63dfe-c88f-43bb-a642-10d75b5a8453
-- title:
--   Planar graphs satisfy the Euler edge bound
-- statement:
--   Every drawable simple graph on at least three finite vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_b1eeea0d_0264_4037_a9be_26c96369c701_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
