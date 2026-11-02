-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_triangulated_supergraph__p2m_cf161613_a0bb_4259_95d5_c320f30b7319_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_triangulated_supergraph__p2m_cf161613_a0bb_4259_95d5_c320f30b7319_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:40:20.90721+00:00
-- url     : https://prove2.me/theorems/14ab409d-ba46-4520-b2b1-fae32ccc2155
-- title:
--   Every drawable graph admits a triangulated planar supergraph
-- statement:
--   Any drawable graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six. This isolates the planar augmentation and triangulation argument needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_triangulated_supergraph__p2m_cf161613_a0bb_4259_95d5_c320f30b7319_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
