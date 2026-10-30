-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_lower_edge_bound__p2m_e54967e0_7450_4934_8f48_f373227ab333_a1
-- name    : WilliamsonShmoys.maximal_planar_completion_lower_edge_bound__p2m_e54967e0_7450_4934_8f48_f373227ab333_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:06:16.943571+00:00
-- url     : https://prove2.me/theorems/a1bc3295-288e-4dac-b293-e5c76a636381
-- title:
--   Lower edge bound for a maximal planar drawing
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on at least three vertices has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_completion_lower_edge_bound__p2m_e54967e0_7450_4934_8f48_f373227ab333_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hMax : forall N : SimpleGraph V, L <= N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N <= L) :
    3 * Fintype.card V <= L.edgeSet.ncard + 6 := by sorry
