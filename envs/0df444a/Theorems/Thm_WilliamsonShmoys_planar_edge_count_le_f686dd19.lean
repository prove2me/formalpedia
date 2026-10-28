-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_le_f686dd19
-- name    : WilliamsonShmoys.planar_edge_count_le_f686dd19
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:29:58.948944+00:00
-- url     : https://prove2.me/theorems/f66312ad-63d7-47ca-b14f-4c0f3cf22e40
-- title:
--   Euler edge bound for a drawable simple graph
-- statement:
--   A simple graph with a crossing-free drawing on a finite linearly ordered vertex type of size at least three has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_le_f686dd19
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry
