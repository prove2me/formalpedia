-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_upper_bound_d974173a
-- name    : WilliamsonShmoys.maximal_drawable_edge_upper_bound_d974173a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:07:42.379003+00:00
-- url     : https://prove2.me/theorems/e2002294-532e-4f58-bb0b-2f40f61d66b4
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every graph with a crossing-free drawing on a finite linearly ordered vertex type of size at least three has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_drawable_edge_upper_bound_d974173a {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
