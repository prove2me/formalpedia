-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_af412bdb_08d3_443e_9526_1f4e854292c2_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_af412bdb_08d3_443e_9526_1f4e854292c2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:23:35.96899+00:00
-- url     : https://prove2.me/theorems/8c9864f5-741a-481d-8578-325697296ee9
-- title:
--   Maximal drawable graph has the planar edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has exactly three times the number of vertices minus six edges. This removes the planar edge-count step from the parent; the proof route is to derive connectedness and triangular faces from maximality, then combine Euler’s formula with the count of face-edge incidences for the given drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_af412bdb_08d3_443e_9526_1f4e854292c2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
