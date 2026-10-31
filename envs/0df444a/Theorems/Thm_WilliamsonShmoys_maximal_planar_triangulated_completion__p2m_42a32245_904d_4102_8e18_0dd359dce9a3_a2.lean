-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulated_completion__p2m_42a32245_904d_4102_8e18_0dd359dce9a3_a2
-- name    : WilliamsonShmoys.maximal_planar_triangulated_completion__p2m_42a32245_904d_4102_8e18_0dd359dce9a3_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:42:37.263856+00:00
-- url     : https://prove2.me/theorems/a8e00233-6ced-4375-a354-4b7099847c43
-- title:
--   Triangulated completion of a planar graph
-- statement:
--   A drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose faces are triangles and whose edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_triangulated_completion__p2m_42a32245_904d_4102_8e18_0dd359dce9a3_a2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 <= Fintype.card V) (hDraw : HasPlanarDrawingOn L) : Exists fun M : SimpleGraph V => L <= M /\ HasPlanarDrawingOn M /\ 3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
