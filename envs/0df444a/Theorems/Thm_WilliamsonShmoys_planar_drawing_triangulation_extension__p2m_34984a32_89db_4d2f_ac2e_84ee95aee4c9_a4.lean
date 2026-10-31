-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_34984a32_89db_4d2f_ac2e_84ee95aee4c9_a4
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_34984a32_89db_4d2f_ac2e_84ee95aee4c9_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:00:45.039309+00:00
-- url     : https://prove2.me/theorems/6a22c569-9038-45af-947c-b97685a49df4
-- title:
--   Triangulation extension of a planar drawing
-- statement:
--   A finite simple graph with at least three vertices and a crossing-free drawing is contained in a graph on the same vertices that also has a crossing-free drawing and exactly 3|V|−6 edges. This stronger statement packages component-joining, face triangulation, and the Euler count. A proof route is to connect components within the plane drawing, add edges inside nontriangular faces until maximal, then count triangular face boundaries using Euler’s formula. The at-least-three-vertices hypothesis avoids the small cases where the triangulated edge formula does not apply.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_34984a32_89db_4d2f_ac2e_84ee95aee4c9_a4 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) : ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
