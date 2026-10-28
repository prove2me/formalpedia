-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_1591b9cd_ac13_4639_82d2_61e7ddbdd660
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_1591b9cd_ac13_4639_82d2_61e7ddbdd660
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T09:44:49.53088+00:00
-- url     : https://prove2.me/theorems/6d31b8fb-3694-4241-bed0-544bfd150e3d
-- title:
--   Euler edge count for a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_1591b9cd_ac13_4639_82d2_61e7ddbdd660
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ J : SimpleGraph V, K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
