-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_abdda8c5_f5c1_4e5d_b801_c7084d469782_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_abdda8c5_f5c1_4e5d_b801_c7084d469782_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:31:15.951967+00:00
-- url     : https://prove2.me/theorems/a37fca92-b240-4415-b2f0-be56bbb8e59b
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A drawable simple graph on at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_abdda8c5_f5c1_4e5d_b801_c7084d469782_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
