-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_edge_count__p2m_b7ddd4a0_5822_4de2_a826_6e2dd80a911f_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_b7ddd4a0_5822_4de2_a826_6e2dd80a911f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:55:16.705106+00:00
-- url     : https://prove2.me/theorems/aea893ff-524d-432f-a94f-a28f6a185e5e
-- title:
--   Planar triangulation completion edge count
-- statement:
--   Every finite drawable simple graph with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly 3|V|−6. This packages completion to a triangulation and the Euler edge count; the hypothesis |V| ≥ 3 handles the small boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion_edge_count__p2m_b7ddd4a0_5822_4de2_a826_6e2dd80a911f_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
