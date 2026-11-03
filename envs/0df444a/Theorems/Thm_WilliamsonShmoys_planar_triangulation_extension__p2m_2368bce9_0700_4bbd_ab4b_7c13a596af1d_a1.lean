-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_2368bce9_0700_4bbd_ab4b_7c13a596af1d_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_2368bce9_0700_4bbd_ab4b_7c13a596af1d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:00:29.439224+00:00
-- url     : https://prove2.me/theorems/64019286-52a7-4945-b306-7d1954508408
-- title:
--   Planar triangulation extension on the same vertex set
-- statement:
--   Every finite simple graph on at least three vertices with the supplied crossing-free drawing has a planar supergraph on the same vertex set whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_2368bce9_0700_4bbd_ab4b_7c13a596af1d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
