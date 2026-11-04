-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edgeCount_upper_connected__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a1
-- name    : WilliamsonShmoys.planar_edgeCount_upper_connected__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:48:28.343218+00:00
-- url     : https://prove2.me/theorems/f36d5627-b6e6-48ed-8d0d-9e5de579a76e
-- title:
--   Edge bound for connected planar drawings
-- statement:
--   A connected simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The three-vertex boundary case is included; connected graphs with fewer vertices are outside this lemma's hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edgeCount_upper_connected__p2m_4d9d61b3_a3d4_4adb_a77f_fb6a2cb8e8dc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hn : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
