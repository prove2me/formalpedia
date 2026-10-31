-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_60b0b6c8_2464_4637_be16_9dc08ca4c2cc_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_60b0b6c8_2464_4637_be16_9dc08ca4c2cc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:06:00.450325+00:00
-- url     : https://prove2.me/theorems/ab4fcf06-6052-4762-83f6-1c588acec272
-- title:
--   Edge bound for a connected simple planar graph
-- statement:
--   A finite connected simple graph with at least three vertices and the supplied crossing-free plane drawing has at most 3V − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_60b0b6c8_2464_4637_be16_9dc08ca4c2cc_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hconn : G.Connected) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
