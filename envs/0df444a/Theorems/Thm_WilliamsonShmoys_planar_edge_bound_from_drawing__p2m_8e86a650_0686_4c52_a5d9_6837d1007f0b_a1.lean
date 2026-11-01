-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_drawing__p2m_8e86a650_0686_4c52_a5d9_6837d1007f0b_a1
-- name    : WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_8e86a650_0686_4c52_a5d9_6837d1007f0b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:55:34.751873+00:00
-- url     : https://prove2.me/theorems/fdaf46ab-4488-466d-ade5-afe997f74795
-- title:
--   Edge bound for every finite drawable simple graph
-- statement:
--   Any finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges. This reusable planar edge bound does not require maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_from_drawing__p2m_8e86a650_0686_4c52_a5d9_6837d1007f0b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry
