-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion__p2m_a74b4731_eea6_44e0_b9ad_6ea707b8b09a_a1
-- name    : WilliamsonShmoys.planar_drawing_completion__p2m_a74b4731_eea6_44e0_b9ad_6ea707b8b09a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:54:34.33829+00:00
-- url     : https://prove2.me/theorems/00e8ebb5-9f6a-4f3b-a13c-8345d9aaf556
-- title:
--   Triangulated planar completion on the same vertex set
-- statement:
--   Any finite simple graph with at least three vertices and a crossing-free drawing is contained, on the same vertex set, in a planar triangulation whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_completion__p2m_a74b4731_eea6_44e0_b9ad_6ea707b8b09a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hDraw : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, M.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
