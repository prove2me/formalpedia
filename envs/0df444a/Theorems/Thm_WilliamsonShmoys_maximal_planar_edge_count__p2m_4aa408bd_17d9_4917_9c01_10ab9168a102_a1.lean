-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4aa408bd_17d9_4917_9c01_10ab9168a102_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_4aa408bd_17d9_4917_9c01_10ab9168a102_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T20:58:39.170992+00:00
-- url     : https://prove2.me/theorems/050d6eed-4305-48ca-94b0-9518ffa2e96b
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict supergraph on the same vertices has exactly `3|V|−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_4aa408bd_17d9_4917_9c01_10ab9168a102_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hMax : ∀ H : SimpleGraph V,
      T.edgeSet ⊆ H.edgeSet →
      HasPlanarDrawingOn H →
      H.edgeSet ⊆ T.edgeSet)
    (hV : 3 <= Fintype.card V) :
    T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
