-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_connected_drawing
-- name    : WilliamsonShmoys.planar_edge_bound_connected_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:14:46.390797+00:00
-- url     : https://prove2.me/theorems/651c26f7-ca80-4806-aa51-a496c589ec2d
-- title:
--   Planar edge bound for connected graphs with a drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges. This isolates the topological step of obtaining the planar graph edge bound from the drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_connected_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
