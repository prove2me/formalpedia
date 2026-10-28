-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_d1313f94_0954_4f2e_9b9e_c37a9ebd0ec4_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_d1313f94_0954_4f2e_9b9e_c37a9ebd0ec4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:13:00.552791+00:00
-- url     : https://prove2.me/theorems/e9f7baec-2042-4774-99e6-a1421ec04a69
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph has exactly `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_d1313f94_0954_4f2e_9b9e_c37a9ebd0ec4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      Set.Subset M.edgeSet N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      Set.Subset N.edgeSet M.edgeSet) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
