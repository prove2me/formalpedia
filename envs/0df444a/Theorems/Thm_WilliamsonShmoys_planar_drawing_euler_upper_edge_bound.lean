-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_upper_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_euler_upper_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:14:23.789612+00:00
-- url     : https://prove2.me/theorems/72392a52-b545-4c3a-965f-477ba946a1b0
-- title:
--   Euler upper bound for a planar drawing
-- statement:
--   Every graph with a planar drawing on at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_upper_edge_bound {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
