-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_04f4db05_702a_494d_b920_fe439899ceaa_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_04f4db05_702a_494d_b920_fe439899ceaa_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:47:39.136275+00:00
-- url     : https://prove2.me/theorems/20aae0e7-47ce-430e-848b-f31970e65b06
-- title:
--   Simple planar graph edge bound
-- statement:
--   A finite connected simple graph with at least three vertices that has the supplied crossing-free plane drawing has at most 3V − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_04f4db05_702a_494d_b920_fe439899ceaa_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hconn : K.Connected) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
