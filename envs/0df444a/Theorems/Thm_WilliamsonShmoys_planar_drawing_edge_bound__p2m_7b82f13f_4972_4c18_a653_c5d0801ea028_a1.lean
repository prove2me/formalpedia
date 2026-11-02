-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:18:20.783614+00:00
-- url     : https://prove2.me/theorems/87ce3ac9-d70a-4a22-9b10-c8d2544e53a0
-- title:
--   Simple planar graph edge bound
-- statement:
--   For a connected simple graph with at least three vertices and the given crossing-free drawing, the number of edges plus six is at most three times the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : Nat.le 3 (Fintype.card V)) :
    Nat.le (H.edgeFinset.card + 6) (3 * Fintype.card V) := by
  sorry
