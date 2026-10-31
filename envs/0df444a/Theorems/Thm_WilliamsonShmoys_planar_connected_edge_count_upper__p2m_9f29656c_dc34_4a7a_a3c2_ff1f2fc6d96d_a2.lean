-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_upper__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2
-- name    : WilliamsonShmoys.planar_connected_edge_count_upper__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:18:37.389133+00:00
-- url     : https://prove2.me/theorems/e072b4d5-a9ae-4f40-9238-0c277accf09b
-- title:
--   Connected planar edge-count upper bound
-- statement:
--   For a connected finite simple graph with a crossing-free drawing and at least three vertices, the edge count is at most three times the vertex count minus six. This isolates the topological core of the target. A proof route is to extract a finite rotation system from the drawing, apply Euler's formula to its faces, and count face-boundary lengths, treating trees and bridges in that count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_edge_count_upper__p2m_9f29656c_dc34_4a7a_a3c2_ff1f2fc6d96d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hConn : M.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
