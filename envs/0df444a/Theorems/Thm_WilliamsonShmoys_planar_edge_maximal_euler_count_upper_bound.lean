-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_euler_count_upper_bound
-- name    : WilliamsonShmoys.planar_edge_maximal_euler_count_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:04:41.111342+00:00
-- url     : https://prove2.me/theorems/f983adb0-d452-4ca3-bbc2-606f811d29c7
-- title:
--   Euler upper bound for a planar drawing
-- statement:
--   A finite simple graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` has at most `3 |V| - 6` edges, expressed without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_maximal_euler_count_upper_bound {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
