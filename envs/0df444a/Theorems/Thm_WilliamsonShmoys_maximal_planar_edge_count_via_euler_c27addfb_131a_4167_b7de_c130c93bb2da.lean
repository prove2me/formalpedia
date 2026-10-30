-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_via_euler_c27addfb_131a_4167_b7de_c130c93bb2da
-- name    : WilliamsonShmoys.maximal_planar_edge_count_via_euler_c27addfb_131a_4167_b7de_c130c93bb2da
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:33:45.402206+00:00
-- url     : https://prove2.me/theorems/1e14b5bf-82fb-4c82-8e45-c8b398b1de74
-- title:
--   Edge count of a maximal drawable graph via Euler's formula
-- statement:
--   An edge-maximal drawable simple graph on at least three finite ordered vertices has exactly three times the number of vertices minus six edges, by the planar-face and Euler argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_via_euler_c27addfb_131a_4167_b7de_c130c93bb2da
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, W ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = W) :
    3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  sorry
