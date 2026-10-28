-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_extension__p2m_b4f3c7d0_f80f_4201_8b80_29190a270a03_a1
-- name    : WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_b4f3c7d0_f80f_4201_8b80_29190a270a03_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:42:12.551545+00:00
-- url     : https://prove2.me/theorems/d1313f94-0954-4f2e-9b9e-c37a9ebd0ec4
-- title:
--   Triangulation extension of a finite planar graph
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices can be extended, using the same vertex set, to a crossing-free graph whose edge count is the triangular planar count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_triangulation_extension__p2m_b4f3c7d0_f80f_4201_8b80_29190a270a03_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
