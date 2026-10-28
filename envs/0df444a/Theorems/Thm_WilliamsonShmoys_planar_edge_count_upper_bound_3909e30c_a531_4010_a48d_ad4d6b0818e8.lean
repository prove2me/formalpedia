-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_3909e30c_a531_4010_a48d_ad4d6b0818e8
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_3909e30c_a531_4010_a48d_ad4d6b0818e8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:29:13.95791+00:00
-- url     : https://prove2.me/theorems/159c3b8a-60f3-4d00-952d-13efc3b8b879
-- title:
--   Euler edge-count upper bound for a drawable graph
-- statement:
--   Every graph admitting the specified crossing-free drawing, on at least three vertices, has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_3909e30c_a531_4010_a48d_ad4d6b0818e8
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    J.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
