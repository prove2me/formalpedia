-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_edge_bound_connected__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a1
-- name    : WilliamsonShmoys.planarDrawing_edge_bound_connected__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:31:22.154211+00:00
-- url     : https://prove2.me/theorems/8700ddcb-5e54-440d-86e0-a8d22ebd60f0
-- title:
--   Edge bound for a connected finite planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most 3n−6 edges. Prove this from the plane embedding’s Euler formula and the lower bound of three on every face boundary walk, accounting for the connected simple cases and bridges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_edge_bound_connected__p2m_af29040b_5f5f_41c7_ae26_98a3e427e1bc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 6 ≤ 3 * Fintype.card V := by sorry
