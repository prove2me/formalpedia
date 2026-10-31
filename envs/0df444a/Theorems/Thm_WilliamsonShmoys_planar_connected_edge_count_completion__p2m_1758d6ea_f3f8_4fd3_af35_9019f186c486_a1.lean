-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_completion__p2m_1758d6ea_f3f8_4fd3_af35_9019f186c486_a1
-- name    : WilliamsonShmoys.planar_connected_edge_count_completion__p2m_1758d6ea_f3f8_4fd3_af35_9019f186c486_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:49:57.364595+00:00
-- url     : https://prove2.me/theorems/3e96e4b7-ffaf-421c-b46f-8949f4d2645c
-- title:
--   Exact edge count for a connected drawable graph completion
-- statement:
--   Every connected drawable simple graph on a finite linearly ordered vertex type with at least three vertices is contained in a drawable supergraph on the same vertices whose edge count is exactly 3|V| − 6. The parent applies this to M and uses maximality to identify the completion with M. The child’s proof route is finite maximal extension followed by triangular faces and Euler’s formula; at three vertices the completion is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_edge_count_completion__p2m_1758d6ea_f3f8_4fd3_af35_9019f186c486_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hConn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
