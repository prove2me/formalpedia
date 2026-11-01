-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_drawing_edge_bound__p2m_e4c5d8ab_7595_4333_b2f6_7c0fac6762c1_a2
-- name    : WilliamsonShmoys.simple_planar_drawing_edge_bound__p2m_e4c5d8ab_7595_4333_b2f6_7c0fac6762c1_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:04:17.455323+00:00
-- url     : https://prove2.me/theorems/602c691a-8d1a-4dfe-88c6-7f0f95c89b91
-- title:
--   Edge bound for a finite graph with a crossing-free drawing
-- statement:
--   Every finite simple graph on at least three vertices with a crossing-free drawing has at most three times its number of vertices minus six edges. This general planar edge bound does not require maximality and applies to disconnected graphs as well.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.simple_planar_drawing_edge_bound__p2m_e4c5d8ab_7595_4333_b2f6_7c0fac6762c1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel _
     G.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
