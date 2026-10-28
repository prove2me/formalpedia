-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_induced_edge_bound
-- name    : WilliamsonShmoys.planar_drawing_connected_induced_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T18:26:29.219287+00:00
-- url     : https://prove2.me/theorems/e085dbcb-1e22-48a3-b906-fed5a9193d37
-- title:
--   Edge bound for a connected induced subgraph of a planar drawing
-- statement:
--   Restrict a crossing-free drawing of a finite ordered simple graph to a connected induced subgraph with at least three vertices; its number of edges plus six is at most three times its number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_induced_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (C : Finset V)
    (hconn : (G.induce (fun v => v ∈ C)).Connected)
    (hcard : 3 ≤ C.card) :
    (G.induce (fun v => v ∈ C)).edgeSet.ncard + 6 ≤ 3 * C.card := by sorry
