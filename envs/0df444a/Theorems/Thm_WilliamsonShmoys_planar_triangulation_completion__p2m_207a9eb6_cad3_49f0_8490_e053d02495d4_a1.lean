-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_207a9eb6_cad3_49f0_8490_e053d02495d4_a1
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_207a9eb6_cad3_49f0_8490_e053d02495d4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:12:43.35291+00:00
-- url     : https://prove2.me/theorems/09b502cd-aaf2-445b-949d-80cdcc13c52d
-- title:
--   Planar triangulation completion on a fixed vertex set
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_207a9eb6_cad3_49f0_8490_e053d02495d4_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) : Exists fun M : SimpleGraph V => Set.Subset H.edgeSet M.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
