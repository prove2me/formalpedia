-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
-- name    : WilliamsonShmoys.planar_connected_edge_bound__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:45:59.734622+00:00
-- url     : https://prove2.me/theorems/f10915d7-3b63-441c-afee-bba7154a1b1e
-- title:
--   Euler edge bound for a connected drawn graph
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges. Prove this using Euler’s relation and the lower bound of three on each face boundary length.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_edge_bound__p2m_4414481d_333a_4f96_8a2d_2d6fda1fe3c0_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hConn : L.Connected) (hV : 3 ≤ Fintype.card V) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
