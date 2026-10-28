-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_completion_edge_count_monotone
-- name    : WilliamsonShmoys.planar_drawing_triangulated_completion_edge_count_monotone
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:06:48.775602+00:00
-- url     : https://prove2.me/theorems/73f1d904-64e0-4086-a55c-e6c5fb5b795d
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite graphs on the same vertex type, graph inclusion implies inclusion of edge sets and therefore monotonicity of their finite edge counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulated_completion_edge_count_monotone
    {V : Type} [Fintype V] [LinearOrder V]
    (G K : SimpleGraph V)
    (hSub : G ≤ K) :
    G.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
