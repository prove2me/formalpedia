-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_bound__p2m_2911e589_9855_41f2_81aa_874f2d2a0dd0_a1
-- name    : WilliamsonShmoys.planar_connected_edge_count_bound__p2m_2911e589_9855_41f2_81aa_874f2d2a0dd0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:39:32.397846+00:00
-- url     : https://prove2.me/theorems/3662a54d-ea7a-4ea3-804a-c2f8a32e2408
-- title:
--   Euler edge bound for connected planar graphs
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most 3n−6 edges. A proof route is to extend it to a maximal planar supergraph, show the resulting faces are triangles, and apply Euler’s formula. The three-vertex boundary case is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_edge_count_bound__p2m_2911e589_9855_41f2_81aa_874f2d2a0dd0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
