-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound
-- name    : WilliamsonShmoys.planar_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T20:29:35.998292+00:00
-- url     : https://prove2.me/theorems/e0cd08bd-ab51-40f1-b30c-4bf4c4e2c635
-- title:
--   Simple planar graphs satisfy the edge bound
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
