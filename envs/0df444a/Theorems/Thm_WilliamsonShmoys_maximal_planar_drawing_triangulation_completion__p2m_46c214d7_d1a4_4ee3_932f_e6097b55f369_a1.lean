-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_triangulation_completion__p2m_46c214d7_d1a4_4ee3_932f_e6097b55f369_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_triangulation_completion__p2m_46c214d7_d1a4_4ee3_932f_e6097b55f369_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:44:17.879755+00:00
-- url     : https://prove2.me/theorems/0fb24e84-44a0-421e-a186-c4879c0fa6ba
-- title:
--   Triangulation completion of a finite planar drawing
-- statement:
--   Every finite planar drawing on at least three vertices can be extended, without adding vertices, to a planar drawing whose graph has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_triangulation_completion__p2m_46c214d7_d1a4_4ee3_932f_e6097b55f369_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
