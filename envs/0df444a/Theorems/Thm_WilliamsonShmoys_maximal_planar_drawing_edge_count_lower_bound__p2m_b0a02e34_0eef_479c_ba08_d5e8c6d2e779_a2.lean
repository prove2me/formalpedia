-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T00:47:30.663865+00:00
-- url     : https://prove2.me/theorems/2098a8ea-ba62-4ffc-b2e7-3164906bb3dd
-- title:
--   Edge count lower bound for a maximal planar drawing
-- statement:
--   A graph maximal under planar supergraph extension, with a drawing satisfying `HasPlanarDrawingOn` and at least three vertices, has at least `3 |V| - 6` edges. Prove this independently by deriving the face structure from the drawing, showing maximality rules out a non-triangular face because a diagonal could be added, then counting triangular face incidences using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  sorry
