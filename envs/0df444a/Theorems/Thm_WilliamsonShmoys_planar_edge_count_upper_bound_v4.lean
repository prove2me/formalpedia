-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_v4
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_v4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:49:22.918564+00:00
-- url     : https://prove2.me/theorems/0908aad3-bf12-4bee-a2ea-0c309ea94f6f
-- title:
--   Edge bound for a drawable simple graph
-- statement:
--   A finite simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V|−6 edges, also when it is disconnected. At |V| = 3, this bound is three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_v4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    (L.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry
