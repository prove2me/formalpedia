-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_954f7585_7fa1_4081_ba59_71da7d8d78f3_a4
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_954f7585_7fa1_4081_ba59_71da7d8d78f3_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T00:29:09.159985+00:00
-- url     : https://prove2.me/theorems/6de9fc5f-7bb3-4620-be35-3e7a3e293de0
-- title:
--   Edge bound for a finite simple planar graph
-- statement:
--   A finite simple graph with at least three vertices that has a crossing-free drawing has at most three times its vertex count minus six edges. This is the classical planar graph edge bound; it can be proved from a planar embedding and Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_954f7585_7fa1_4081_ba59_71da7d8d78f3_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
