-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_connected_c61b3391
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_connected_c61b3391
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:08:31.646588+00:00
-- url     : https://prove2.me/theorems/ca7c3223-894c-4525-8a1e-91af08cc954a
-- title:
--   Euler bound for a connected finite simple planar graph
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges. This isolates the planar topology and Euler-counting step. A proof route is to extend a connected drawing to a triangulation on the same vertices, then use Euler’s formula; the extension handles bridges and tree cases that invalidate a naïve lower bound on every face boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_connected_c61b3391
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
