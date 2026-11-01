-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_710ae9cd_06e1_4ca5_a820_3c02fa6bdb35_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_710ae9cd_06e1_4ca5_a820_3c02fa6bdb35_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:13:43.765757+00:00
-- url     : https://prove2.me/theorems/b9db41c8-79f8-4b68-86df-fe1252530a28
-- title:
--   Edge bound for a finite simple graph with a planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_710ae9cd_06e1_4ca5_a820_3c02fa6bdb35_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
