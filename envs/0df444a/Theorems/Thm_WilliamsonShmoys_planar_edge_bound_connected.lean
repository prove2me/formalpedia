-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_connected
-- name    : WilliamsonShmoys.planar_edge_bound_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:44:41.523509+00:00
-- url     : https://prove2.me/theorems/fd8b95ea-6756-4b6e-95bb-f503adb1bdc1
-- title:
--   The edge bound for connected planar graphs
-- statement:
--   Every connected finite simple graph on at least three vertices with the stated crossing-free drawing has at most 3|V|−6 edges. This removes the connected case’s edge-count argument from the parent. A proof route is to extend the connected planar graph to a triangulated planar supergraph on the same vertices, then combine Euler’s formula with the fact that every face has boundary length at least three. The size hypothesis is essential for this face-count argument and matches the parent’s exact bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hconn : M.Connected)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
