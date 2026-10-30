-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:05:05.888034+00:00
-- url     : https://prove2.me/theorems/c94121e2-adc9-4018-a433-d3dee737ddb5
-- title:
--   Complete a planar drawing to the maximal planar edge count
-- statement:
--   Every drawable simple graph on a finite ordered vertex set of size at least three has a drawable supergraph on the same vertices with exactly $3|V|-6$ edges. The lower bound includes the boundary case of three vertices, where the completion is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
