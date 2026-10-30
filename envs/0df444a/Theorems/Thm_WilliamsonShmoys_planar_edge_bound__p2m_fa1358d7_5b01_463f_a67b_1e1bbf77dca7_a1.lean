-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_fa1358d7_5b01_463f_a67b_1e1bbf77dca7_a1
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_fa1358d7_5b01_463f_a67b_1e1bbf77dca7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:12:24.293003+00:00
-- url     : https://prove2.me/theorems/66ade5d4-3842-4532-bbd5-36e43a15d1f5
-- title:
--   Euler edge bound for a graph with a crossing-free drawing
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_bound__p2m_fa1358d7_5b01_463f_a67b_1e1bbf77dca7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
