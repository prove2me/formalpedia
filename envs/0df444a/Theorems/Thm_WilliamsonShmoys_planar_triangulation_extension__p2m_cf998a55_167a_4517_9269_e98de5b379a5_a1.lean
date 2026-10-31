-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_cf998a55_167a_4517_9269_e98de5b379a5_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_cf998a55_167a_4517_9269_e98de5b379a5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:55:23.870059+00:00
-- url     : https://prove2.me/theorems/41a2d92d-f309-4ef2-a3ac-f99a2b15ffbc
-- title:
--   Extend a planar drawing to a triangulated graph
-- statement:
--   Any drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertex set whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_cf998a55_167a_4517_9269_e98de5b379a5_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ T : SimpleGraph V, (∀ u v, K.Adj u v → T.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
