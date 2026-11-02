-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing__p2m_4c570e3e_7abb_4bee_95ce_463a755b298b_a2
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_4c570e3e_7abb_4bee_95ce_463a755b298b_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T16:46:26.307921+00:00
-- url     : https://prove2.me/theorems/2a9426af-e394-457d-867f-287403a9288d
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   An inclusion-maximal drawable graph on a finite linearly ordered vertex type with at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_4c570e3e_7abb_4bee_95ce_463a755b298b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 = H.edgeFinset.card := by sorry
