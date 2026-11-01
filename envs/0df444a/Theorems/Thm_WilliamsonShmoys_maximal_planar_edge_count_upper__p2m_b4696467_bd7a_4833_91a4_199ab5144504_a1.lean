-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:08:10.7442+00:00
-- url     : https://prove2.me/theorems/b865fe19-b86f-4742-89c9-6df3d0fd3be8
-- title:
--   Planar simple graph edge-count upper bound
-- statement:
--   Any drawable simple graph on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_b4696467_bd7a_4833_91a4_199ab5144504_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
