-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_upper_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_edge_upper_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:21:30.945497+00:00
-- url     : https://prove2.me/theorems/d7bd9f42-660b-4a90-ad96-8742076e0509
-- title:
--   Simple connected planar graphs satisfy the edge bound
-- statement:
--   A finite simple graph with at least three vertices and a connected crossing-free plane drawing has at most 3n − 6 edges. The standard route uses Euler’s formula and facial boundary lengths; the connectedness premise needed for that route is supplied by the parent theorem, so this child should include connectedness as a hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_edge_upper_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) ≤ 3 * Fintype.card V - 6 := by sorry
