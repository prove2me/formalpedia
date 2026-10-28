-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_96b612ce_7021_404c_8189_06955c76f0dc_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_96b612ce_7021_404c_8189_06955c76f0dc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:47:10.566918+00:00
-- url     : https://prove2.me/theorems/19289cd0-8bc0-4354-9e78-5126f5795da0
-- title:
--   Edge lower bound for an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least `3 * |V| - 6` edges, expressed without truncated subtraction. The proof route is to show maximality forces connectedness and triangular faces, then apply Euler’s formula and count face-edge incidences. This isolates the main topological work; combined with the maximal extension lemma, it contradicts the parent’s strict edge-count hypothesis if the extension were equal to the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_96b612ce_7021_404c_8189_06955c76f0dc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
