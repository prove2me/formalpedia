-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_bound_retry3
-- name    : WilliamsonShmoys.planar_edge_count_bound_retry3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:31:17.735643+00:00
-- url     : https://prove2.me/theorems/e46e8dd0-1680-4d93-a7d5-10e0bd7d8348
-- title:
--   Planar edge count bound
-- statement:
--   A drawable simple graph on at least three finite vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_bound_retry3 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 <= Fintype.card V) : G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
