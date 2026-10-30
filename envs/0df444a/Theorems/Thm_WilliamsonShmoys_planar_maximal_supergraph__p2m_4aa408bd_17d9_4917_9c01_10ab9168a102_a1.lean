-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_4aa408bd_17d9_4917_9c01_10ab9168a102_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph__p2m_4aa408bd_17d9_4917_9c01_10ab9168a102_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T20:58:37.30018+00:00
-- url     : https://prove2.me/theorems/30b6c010-ab73-46dd-b2c7-d549b3a8cd09
-- title:
--   Maximal drawable supergraph on a fixed vertex set
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under edge-set inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph__p2m_4aa408bd_17d9_4917_9c01_10ab9168a102_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    Exists fun T : SimpleGraph V =>
      And (G.edgeSet ⊆ T.edgeSet)
        (And (HasPlanarDrawingOn T)
          (∀ H : SimpleGraph V,
            T.edgeSet ⊆ H.edgeSet →
            HasPlanarDrawingOn H →
            H.edgeSet ⊆ T.edgeSet)) := by
  sorry
