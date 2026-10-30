-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_5de67bd5_1b50_462c_9c5e_b0f0f644e7f0_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_5de67bd5_1b50_462c_9c5e_b0f0f644e7f0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T10:03:12.537135+00:00
-- url     : https://prove2.me/theorems/eaf34b86-d68e-41ae-88a7-671659ded126
-- title:
--   Euler upper bound for a finite planar simple graph
-- statement:
--   For a finite simple graph with a crossing-free drawing and at least three vertices, its edge count is at most three times its vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_5de67bd5_1b50_462c_9c5e_b0f0f644e7f0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ (Set.univ : Set V).ncard) :
    N.edgeSet.ncard + 6 ≤ 3 * (Set.univ : Set V).ncard := by sorry
