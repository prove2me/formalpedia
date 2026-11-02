-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count__p2m_d5765fc6_2061_49c6_883d_a2bbbc9ebfd2_a4
-- name    : WilliamsonShmoys.planar_completion_edge_count__p2m_d5765fc6_2061_49c6_883d_a2bbbc9ebfd2_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:44:39.495002+00:00
-- url     : https://prove2.me/theorems/ea7f7d9d-b42f-43dd-b02c-ace5f69dfba5
-- title:
--   Planar completion with the maximal planar edge count
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex set, with a finite edge set, whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_edge_count__p2m_d5765fc6_2061_49c6_883d_a2bbbc9ebfd2_a4 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V) (hplanar : HasPlanarDrawingOn G) : ∃ (K : SimpleGraph V) (hKfin : Fintype K.edgeSet), G ≤ K ∧ HasPlanarDrawingOn K ∧ (@SimpleGraph.edgeFinset V K hKfin).card + 6 = 3 * Fintype.card V := by sorry
