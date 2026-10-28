-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_bound_552f0216_da27_4340_ada6_5c47a5b50119
-- name    : WilliamsonShmoys.planar_drawing_edge_count_bound_552f0216_da27_4340_ada6_5c47a5b50119
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:24:56.006577+00:00
-- url     : https://prove2.me/theorems/beb3fd77-7f9e-4f2a-a487-845077ff9492
-- title:
--   Euler edge bound for a finite simple graph with a planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_bound_552f0216_da27_4340_ada6_5c47a5b50119 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
