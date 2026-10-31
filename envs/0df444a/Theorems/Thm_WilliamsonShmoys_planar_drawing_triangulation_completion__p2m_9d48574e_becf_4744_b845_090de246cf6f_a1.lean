-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:20:41.577121+00:00
-- url     : https://prove2.me/theorems/6ab13955-ca33-41a0-b892-672767e48ad0
-- title:
--   Triangulation completion of a finite planar drawing
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) (hV : 3 ≤ Fintype.card V) : ∃ R : SimpleGraph V, Q ≤ R ∧ HasPlanarDrawingOn R ∧ R.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
