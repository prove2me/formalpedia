-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_of_connected
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_of_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:14:57.041025+00:00
-- url     : https://prove2.me/theorems/06d1a42f-b4b2-4bca-b472-a443773488ce
-- title:
--   Simple planar drawing edge bound for walk-connected graphs
-- statement:
--   A finite simple graph with the specified crossing-free drawing and a walk between every pair of vertices has at most three times its number of vertices minus six edges, when it has at least three vertices. This isolates the connected planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_of_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v)) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
