-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulated_supergraph__p2m_19dec27f_df1a_4e90_89f3_8f6e92e830e3_a1
-- name    : WilliamsonShmoys.planar_drawingOn_triangulated_supergraph__p2m_19dec27f_df1a_4e90_89f3_8f6e92e830e3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:55:41.20824+00:00
-- url     : https://prove2.me/theorems/ac4b6b7c-6a36-45ce-9f61-962873444f22
-- title:
--   Planar drawing admits a triangulated supergraph
-- statement:
--   Any crossing-free drawing on a finite linearly ordered vertex type with at least three vertices can be extended, on the same vertices, to a planar graph whose edge count is three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_triangulated_supergraph__p2m_19dec27f_df1a_4e90_89f3_8f6e92e830e3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
