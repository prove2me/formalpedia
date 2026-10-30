-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_7592409d_0b44_4594_9ed9_df868002d7c4_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_7592409d_0b44_4594_9ed9_df868002d7c4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:01:11.619084+00:00
-- url     : https://prove2.me/theorems/32d64e78-128c-439f-8abe-646fa9377720
-- title:
--   Planar drawing edge upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges. This child supplies the upper bound on the target’s edge count. A proof route is to use Euler’s formula for each connected component of the embedded graph, accounting separately for tree components and then summing the resulting bounds; the hypothesis n ≥ 3 supplies the small-vertex boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_7592409d_0b44_4594_9ed9_df868002d7c4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 <= Fintype.card V) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
