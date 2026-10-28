-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_edge_bound_target
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_target
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:49:09.450225+00:00
-- url     : https://prove2.me/theorems/91cda3a8-2cc6-4a3a-811a-1abeffdfb86e
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A maximal graph admitting the given planar drawing, with at least three vertices, has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count_for_edge_bound_target {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
