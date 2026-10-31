-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_maximal_planar__p2m_3eaf26d3_b02e_4c77_b998_3e9af8fb07e7_a1
-- name    : WilliamsonShmoys.planar_drawing_extends_to_maximal_planar__p2m_3eaf26d3_b02e_4c77_b998_3e9af8fb07e7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:16:14.600119+00:00
-- url     : https://prove2.me/theorems/e7bfefe9-c4cd-4b0d-b2f1-de0e94ecd613
-- title:
--   Extend a finite planar drawing to a maximal planar graph
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has a planar supergraph on the same vertices whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_extends_to_maximal_planar__p2m_3eaf26d3_b02e_4c77_b998_3e9af8fb07e7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      M.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
