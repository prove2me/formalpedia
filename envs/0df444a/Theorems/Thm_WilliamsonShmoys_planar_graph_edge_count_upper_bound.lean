-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound
-- name    : WilliamsonShmoys.planar_graph_edge_count_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:46:51.914645+00:00
-- url     : https://prove2.me/theorems/4881293e-7bf5-4184-9f0b-57a8f75b0b6d
-- title:
--   Planar graph edge upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
