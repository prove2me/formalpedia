-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_30a2cd75
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_30a2cd75
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:57:12.116037+00:00
-- url     : https://prove2.me/theorems/66e594d2-cb5c-4a09-8145-3dd71ccc0d91
-- title:
--   Edge bound for a finite drawable simple graph
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3n−6 edges, whether or not it is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_upper_bound_30a2cd75 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) : M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
