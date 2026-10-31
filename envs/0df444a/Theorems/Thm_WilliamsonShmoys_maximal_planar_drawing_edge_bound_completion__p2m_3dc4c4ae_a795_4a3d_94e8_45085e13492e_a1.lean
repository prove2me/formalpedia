-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_completion__p2m_3dc4c4ae_a795_4a3d_94e8_45085e13492e_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound_completion__p2m_3dc4c4ae_a795_4a3d_94e8_45085e13492e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:28:51.198331+00:00
-- url     : https://prove2.me/theorems/34be30da-42b8-40a1-89e9-f0ba3aa7e7d4
-- title:
--   Edge bound for a planar completion
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with at least `3n − 6` edges. The completion may be obtained by adding drawable edges until the graph is maximal, then applying the maximal planar graph edge bound. This is a useful completion result for arbitrary planar graphs; the topological edge bound for the saturated completion remains the main obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound_completion__p2m_3dc4c4ae_a795_4a3d_94e8_45085e13492e_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ 3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry
