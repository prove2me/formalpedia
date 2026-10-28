-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_ws
-- name    : WilliamsonShmoys.planar_edge_upper_bound_ws
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:37:48.452208+00:00
-- url     : https://prove2.me/theorems/76c4ca49-7210-4b7f-ad65-0ea9cadea2bb
-- title:
--   Planar edge upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound_ws {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 ≤ Fintype.card V) : M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
