-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_638ff1ed_8b53_4df9_8415_0aa43fe61583_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_638ff1ed_8b53_4df9_8415_0aa43fe61583_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:22:34.893253+00:00
-- url     : https://prove2.me/theorems/2732a158-7c47-4798-8446-4021e87baee8
-- title:
--   Triangulated completion of a finite planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has a planar triangulated completion on the same vertex type that contains every original edge and has exactly 3|V|−6 edges. This isolates the drawing-to-triangulation topology from the parent’s short counting argument. Its independent proof route is to join distinct components through faces and then add noncrossing diagonals until every face is triangular. For three vertices the completion is the triangle; the stated cardinality hypothesis excludes smaller boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_638ff1ed_8b53_4df9_8415_0aa43fe61583_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 <= Fintype.card V) (hHplanar : HasPlanarDrawingOn H) : ∃ T : SimpleGraph V, H ≤ T ∧ H.edgeSet ⊆ T.edgeSet ∧ T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
