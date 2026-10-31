-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion__p2m_a893531d_2eaf_40a4_93f3_f4bc4ca725ea_a3
-- name    : WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_a893531d_2eaf_40a4_93f3_f4bc4ca725ea_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:31:24.747108+00:00
-- url     : https://prove2.me/theorems/7cbc47d5-f864-41b7-a55a-235c34cff0ec
-- title:
--   Triangulated planar completion of a drawable graph
-- statement:
--   For a finite drawable simple graph with at least three vertices, there is a drawable simple supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six. The explicit edge-count inequality records the monotonicity needed by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_completion__p2m_a893531d_2eaf_40a4_93f3_f4bc4ca725ea_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
