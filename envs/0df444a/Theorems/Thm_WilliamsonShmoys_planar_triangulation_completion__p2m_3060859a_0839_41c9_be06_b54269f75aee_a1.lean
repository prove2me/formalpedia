-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_3060859a_0839_41c9_be06_b54269f75aee_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_3060859a_0839_41c9_be06_b54269f75aee_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:27:14.597334+00:00
-- url     : https://prove2.me/theorems/54bfa514-b5d2-470b-aa39-b977e5665440
-- title:
--   Planar triangulation completion with exact edge count
-- statement:
--   Any drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_3060859a_0839_41c9_be06_b54269f75aee_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hPlanar : HasPlanarDrawingOn J) :
    ∃ N : SimpleGraph V,
      J ≤ N ∧
      HasPlanarDrawingOn N ∧
      3 * Fintype.card V - 6 = N.edgeSet.ncard := by sorry
