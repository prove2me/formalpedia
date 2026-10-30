-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_ff597491
-- name    : WilliamsonShmoys.planar_completion_edge_count_ff597491
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:11:49.797273+00:00
-- url     : https://prove2.me/theorems/2bfcc8bb-6993-4bf2-bb41-6ff6b0efc4c5
-- title:
--   Completion to a maximal planar edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices is a subgraph of a drawable graph on the same vertex type whose edge count is exactly `3n − 6`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_edge_count_ff597491 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
