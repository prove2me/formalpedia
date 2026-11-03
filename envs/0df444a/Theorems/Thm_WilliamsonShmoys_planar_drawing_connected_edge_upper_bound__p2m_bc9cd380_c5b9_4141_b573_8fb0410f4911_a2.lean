-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_upper_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_edge_upper_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:35:27.698434+00:00
-- url     : https://prove2.me/theorems/7a360dd1-f532-43f5-9311-c0e08115dae5
-- title:
--   Connected simple planar graphs satisfy the edge bound
-- statement:
--   This child is the planar extremal edge bound needed by the parent. It retains connectedness and the three-vertex lower bound required by the facial-boundary argument. A source-faithful proof constructs the embedding data from the crossing-free drawing, applies Euler's formula, counts two directed incidences per edge, and uses that each facial boundary walk has length at least three for a connected simple planar graph with at least three vertices. The case of exactly three vertices is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_edge_upper_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) ≤ 3 * Fintype.card V - 6 := by sorry
