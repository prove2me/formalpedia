-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper
-- name    : WilliamsonShmoys.planar_edge_count_upper
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:00:48.543206+00:00
-- url     : https://prove2.me/theorems/552f0216-da27-4340-ada6-5c47a5b50119
-- title:
--   Euler upper bound for drawable simple graphs
-- statement:
--   Every graph with the specified crossing-free drawing on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hcard : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
