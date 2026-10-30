-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_edge_bound_for_finite_simple_graph
-- name    : WilliamsonShmoys.planar_drawing_euler_edge_bound_for_finite_simple_graph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:01:47.042529+00:00
-- url     : https://prove2.me/theorems/ebe90c44-ff54-4015-b7bb-f37708f52e3b
-- title:
--   Euler edge bound for a finite simple graph with a crossing-free drawing
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_edge_bound_for_finite_simple_graph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
