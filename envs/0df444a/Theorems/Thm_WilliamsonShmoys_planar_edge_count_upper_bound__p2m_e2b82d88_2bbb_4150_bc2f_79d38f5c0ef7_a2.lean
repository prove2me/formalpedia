-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:59:17.757215+00:00
-- url     : https://prove2.me/theorems/6301d38c-0224-4362-a676-de729a46b58e
-- title:
--   Planar graph edge upper bound
-- statement:
--   For a finite simple graph with a crossing-free drawing and at least three vertices, the number of edges is at most `3n−6`. This isolates the general planar upper bound from maximality. A proof route is Euler’s formula and face-edge counting, with component counting for disconnected graphs; when `n=3`, the claim reduces to the simple-graph bound of three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_e2b82d88_2bbb_4150_bc2f_79d38f5c0ef7_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    N.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
