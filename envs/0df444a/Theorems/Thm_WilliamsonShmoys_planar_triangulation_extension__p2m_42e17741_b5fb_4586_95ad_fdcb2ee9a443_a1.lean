-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_42e17741_b5fb_4586_95ad_fdcb2ee9a443_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_42e17741_b5fb_4586_95ad_fdcb2ee9a443_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:44:04.013142+00:00
-- url     : https://prove2.me/theorems/3e222915-cdcc-42d9-bbed-07142c562af3
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph of a drawable graph on the same vertex type having exactly 3|V|−6 edges. The three-vertex boundary case is covered: the extension can be the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_42e17741_b5fb_4586_95ad_fdcb2ee9a443_a1 {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V) (hW : WilliamsonShmoys.HasPlanarDrawingOn W) (hV : 3 ≤ Fintype.card V) : ∃ X : SimpleGraph V, W ≤ X ∧ WilliamsonShmoys.HasPlanarDrawingOn X ∧ X.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
