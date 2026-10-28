-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_d974173a
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_d974173a
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T15:45:00.980528+00:00
-- url     : https://prove2.me/theorems/7da6b326-4044-4bf2-887c-5e8fae5569c7
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_drawable_edge_count_d974173a {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) : 3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
