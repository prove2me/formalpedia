-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_with_euler_edge_count
-- name    : WilliamsonShmoys.maximal_planar_supergraph_with_euler_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:58:36.52887+00:00
-- url     : https://prove2.me/theorems/617fe75d-619a-4d40-b3ba-9dc9c387c537
-- title:
--   Planar supergraph with maximal planar edge count
-- statement:
--   Every graph with the supplied planar drawing on at least three vertices is contained in a drawable simple graph on the same vertex type whose edge count is exactly three times the number of vertices minus six. The equation is written with addition to avoid truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_with_euler_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * Fintype.card V = N.edgeSet.ncard + 6 := by sorry
