-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_18203136_f8d0_4c28_bbe0_f08319907a9f_a1
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_18203136_f8d0_4c28_bbe0_f08319907a9f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:47:08.969492+00:00
-- url     : https://prove2.me/theorems/0fddcf0a-fce4-46f9-ad91-85458f71373c
-- title:
--   Exact edge-count completion of a drawable graph
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertices with exactly 3|V| − 6 edges. This reusable completion lemma carries the topological triangulation and Euler-counting work; the parent then uses maximality to show the completion equals the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_18203136_f8d0_4c28_bbe0_f08319907a9f_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
