-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T12:59:47.138125+00:00
-- url     : https://prove2.me/theorems/a35bc758-b19f-4723-ab77-549993b145fc
-- title:
--   Edge upper bound for a planar drawing
-- statement:
--   A drawable simple graph on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_d800a379_5df5_4e36_a12d_7e3e08fd9483_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
