-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_18fad212_36ea_4c15_83d2_5b7bd6c85e9a_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_18fad212_36ea_4c15_83d2_5b7bd6c85e9a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:54:37.42221+00:00
-- url     : https://prove2.me/theorems/ffc13159-3620-43e0-97b9-474801033c8c
-- title:
--   Triangulation extension of a planar drawing
-- statement:
--   Any drawable simple graph on at least three vertices can be extended on the same vertex set to a drawable graph with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_18fad212_36ea_4c15_83d2_5b7bd6c85e9a_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ J : SimpleGraph V, H ≤ J ∧ WilliamsonShmoys.HasPlanarDrawingOn J ∧ J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
