-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_count_completion__p2m_4d6c0a35_6002_42fd_b1db_c7f140706d86_a1
-- name    : WilliamsonShmoys.planar_drawing_has_edge_count_completion__p2m_4d6c0a35_6002_42fd_b1db_c7f140706d86_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:45:06.414416+00:00
-- url     : https://prove2.me/theorems/252969a2-5705-4ea9-b97e-d995b4f5b608
-- title:
--   Every finite planar drawing has a maximal edge-count completion
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertices with exactly 3n − 6 edges. This packages the triangulation completion and Euler count; the parent’s maximality hypothesis then identifies the completion with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_edge_count_completion__p2m_4d6c0a35_6002_42fd_b1db_c7f140706d86_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
