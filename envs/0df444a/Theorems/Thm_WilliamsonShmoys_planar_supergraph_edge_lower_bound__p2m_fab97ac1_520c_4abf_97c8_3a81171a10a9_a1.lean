-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound__p2m_fab97ac1_520c_4abf_97c8_3a81171a10a9_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_fab97ac1_520c_4abf_97c8_3a81171a10a9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:25:46.328072+00:00
-- url     : https://prove2.me/theorems/73c11356-224a-46ad-adf9-93b5e9cc00b6
-- title:
--   Planar supergraph reaches the edge lower bound
-- statement:
--   Every finite simple graph with a planar drawing on at least three vertices has a planar supergraph on the same vertex set with at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_fab97ac1_520c_4abf_97c8_3a81171a10a9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
