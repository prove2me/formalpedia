-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_repair2
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_repair2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:15:09.83959+00:00
-- url     : https://prove2.me/theorems/c73cf9ba-fcca-4a3b-853a-2c4df1119a23
-- title:
--   Euler edge bound for a finite planar drawing
-- statement:
--   A graph with the specified crossing-free drawing on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_repair2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
