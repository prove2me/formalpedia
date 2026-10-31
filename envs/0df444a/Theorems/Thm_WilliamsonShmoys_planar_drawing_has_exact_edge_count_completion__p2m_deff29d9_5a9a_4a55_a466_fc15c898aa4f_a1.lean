-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_count_completion__p2m_deff29d9_5a9a_4a55_a466_fc15c898aa4f_a1
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_deff29d9_5a9a_4a55_a466_fc15c898aa4f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:05:29.01017+00:00
-- url     : https://prove2.me/theorems/7cf6806e-5be6-4790-8cad-719b856f9dab
-- title:
--   Completion of a planar drawing to the maximal planar edge count
-- statement:
--   Any drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_count_completion__p2m_deff29d9_5a9a_4a55_a466_fc15c898aa4f_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
