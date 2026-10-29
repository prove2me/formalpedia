-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_v2__p2m_44371095_5c9f_4251_8e40_79aa61922fda_a4
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_v2__p2m_44371095_5c9f_4251_8e40_79aa61922fda_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T00:26:06.366891+00:00
-- url     : https://prove2.me/theorems/1b8ea8dd-99bc-4e7e-aeca-9707a03ee4e9
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph with at least three vertices has exactly `3 * |V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_v2__p2m_44371095_5c9f_4251_8e40_79aa61922fda_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
