-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_upper_bound
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:41:28.992989+00:00
-- url     : https://prove2.me/theorems/9e70b1f3-beb8-4e29-b349-951e8bf8e927
-- title:
--   Planar graph edge count upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_upper_bound {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDrawing : HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
