-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1
-- name    : WilliamsonShmoys.planar_connected_edge_bound__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:53:57.555974+00:00
-- url     : https://prove2.me/theorems/82dc859a-8068-4b67-a69e-69714826e35e
-- title:
--   Connected planar graph edge bound
-- statement:
--   A finite simple connected graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_edge_bound__p2m_2e520467_0d96_4c71_b340_b60069871ecd_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hconn : H.Connected) (hV : 3 <= Fintype.card V) : H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
