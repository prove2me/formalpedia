-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_f1bfaff0_3b11_4c21_8672_bb1e9fe098b3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper_f1bfaff0_3b11_4c21_8672_bb1e9fe098b3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:32:13.152897+00:00
-- url     : https://prove2.me/theorems/c2a5f0e8-d956-45e0-9a36-664b714000f5
-- title:
--   Euler upper bound for a planar graph
-- statement:
--   Any graph with the supplied planar drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_upper_f1bfaff0_3b11_4c21_8672_bb1e9fe098b3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
