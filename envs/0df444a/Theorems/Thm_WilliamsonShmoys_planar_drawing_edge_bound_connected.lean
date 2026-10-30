-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_connected
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:20:54.017139+00:00
-- url     : https://prove2.me/theorems/4091134b-234a-4ff0-b75c-a1bd78509636
-- title:
--   Planar drawing edge bound for connected graphs
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_connected
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hconn : T.Connected)
    (hV : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
