-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_induced_edge_bound__p2m_e7b88b3e_57d2_4e16_879b_dc797a764fee_a1
-- name    : WilliamsonShmoys.planar_induced_edge_bound__p2m_e7b88b3e_57d2_4e16_879b_dc797a764fee_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:23:44.46653+00:00
-- url     : https://prove2.me/theorems/6e4e017e-bab7-47b3-83d0-5d7ff158d342
-- title:
--   Planar induced subgraph edge bound
-- statement:
--   For any finite vertex subset of a graph with a crossing-free drawing, the induced subgraph has at most \(3n-6\) edges when it has at least three vertices, at most one edge when it has two vertices, and no edges when it has fewer than two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Finset

theorem WilliamsonShmoys.planar_induced_edge_bound__p2m_e7b88b3e_57d2_4e16_879b_dc797a764fee_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (s : Finset V) :
    if 3 ≤ s.card then
      (L.induce (fun v => v ∈ s)).edgeSet.ncard ≤ 3 * s.card - 6
    else if 2 ≤ s.card then
      (L.induce (fun v => v ∈ s)).edgeSet.ncard ≤ 1
    else
      (L.induce (fun v => v ∈ s)).edgeSet.ncard = 0 := by sorry
