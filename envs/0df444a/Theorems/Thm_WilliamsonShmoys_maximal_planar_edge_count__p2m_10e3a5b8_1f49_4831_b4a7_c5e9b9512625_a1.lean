-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_10e3a5b8_1f49_4831_b4a7_c5e9b9512625_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_10e3a5b8_1f49_4831_b4a7_c5e9b9512625_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:23.124896+00:00
-- url     : https://prove2.me/theorems/05b862e6-965f-4ca7-859a-791049e91053
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite vertex set of size at least three has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_10e3a5b8_1f49_4831_b4a7_c5e9b9512625_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M)
    (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
