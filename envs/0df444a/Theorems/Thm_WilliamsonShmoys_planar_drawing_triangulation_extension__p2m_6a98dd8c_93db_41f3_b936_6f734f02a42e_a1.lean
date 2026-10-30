-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension__p2m_6a98dd8c_93db_41f3_b936_6f734f02a42e_a1
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_6a98dd8c_93db_41f3_b936_6f734f02a42e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:41:32.40716+00:00
-- url     : https://prove2.me/theorems/dc9018d8-e47b-47c1-8eef-84ccb4273562
-- title:
--   Planar drawing extension to a triangulation
-- statement:
--   Every planar drawing on a finite linearly ordered vertex type with at least three vertices has a planar supergraph on the same vertices with exactly 3|V|−6 edges. The boundary case |V|=3 is consistent: the extension is a triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension__p2m_6a98dd8c_93db_41f3_b936_6f734f02a42e_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ T : SimpleGraph V, G ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
