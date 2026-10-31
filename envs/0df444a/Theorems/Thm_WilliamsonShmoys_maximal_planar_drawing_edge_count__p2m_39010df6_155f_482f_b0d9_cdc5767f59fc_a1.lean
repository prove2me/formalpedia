-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_39010df6_155f_482f_b0d9_cdc5767f59fc_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_39010df6_155f_482f_b0d9_cdc5767f59fc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:32:21.529339+00:00
-- url     : https://prove2.me/theorems/e59a889d-669c-414e-8ddd-df780e6fdba8
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   A drawable simple graph on at least three finite vertices that has no proper drawable supergraph has exactly `3|V|−6` edges. The boundary case of three vertices is the complete triangle. A proof route is to show maximality forces connectedness and triangular faces in a planar embedding, then apply Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_39010df6_155f_482f_b0d9_cdc5767f59fc_a1 {V : Type} [Fintype V] [LinearOrder V] (Y : SimpleGraph V) (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) (hV : 3 ≤ Fintype.card V) (hMax : ∀ Z : SimpleGraph V, Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Y = Z) : Y.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
