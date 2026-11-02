-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound__p2m_f302bffe_a312_4c80_ba34_5d3904b8242e_a1
-- name    : WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound__p2m_f302bffe_a312_4c80_ba34_5d3904b8242e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:55:57.677507+00:00
-- url     : https://prove2.me/theorems/fab97ac1-520c-4abf-97c8-3a81171a10a9
-- title:
--   Maximality forces the planar edge lower bound
-- statement:
--   An inclusion-maximal finite simple planar graph on at least three vertices has at least 3n−6 edges. Maximality excludes adding any edge while preserving a planar drawing; the standard route is to show the drawing is connected and every face is triangular, then use Euler's formula and edge-face incidence. This supplies the lower-counting half independently of the Euler upper bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys_maximal_planar_graph_edge_count_lower_bound__p2m_f302bffe_a312_4c80_ba34_5d3904b8242e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
