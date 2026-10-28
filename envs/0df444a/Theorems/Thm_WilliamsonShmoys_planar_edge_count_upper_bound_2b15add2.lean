-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_2b15add2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_2b15add2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:46:25.739137+00:00
-- url     : https://prove2.me/theorems/4e878c42-401b-4f48-a394-61656642aa09
-- title:
--   Euler upper bound for a planar simple graph
-- statement:
--   Every graph with the specified crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges. This isolates the standard Euler upper bound. A proof route is to use the planar Euler formula together with simplicity, which ensures every face boundary has length at least three (with the small-vertex boundary handled by the hypothesis).
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_2b15add2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
