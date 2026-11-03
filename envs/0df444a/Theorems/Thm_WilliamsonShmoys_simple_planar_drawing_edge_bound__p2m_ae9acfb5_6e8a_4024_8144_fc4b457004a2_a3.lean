-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_drawing_edge_bound__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3
-- name    : WilliamsonShmoys.simple_planar_drawing_edge_bound__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:02:44.352057+00:00
-- url     : https://prove2.me/theorems/376b67ec-1efe-4ea0-9e38-4777b8820599
-- title:
--   Edge bound for a connected simple planar drawing
-- statement:
--   A connected simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.simple_planar_drawing_edge_bound__p2m_ae9acfb5_6e8a_4024_8144_fc4b457004a2_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  sorry
