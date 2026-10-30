-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T18:53:15.90876+00:00
-- url     : https://prove2.me/theorems/47dd4d29-39eb-42d2-bcda-067ac8d38a8a
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph__p2m_9cc0c9d9_a289_45c0_90c4_3b812fbd190b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      Set.Subset G.edgeSet M.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V,
        Set.Subset M.edgeSet N.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn N → N = M := by
  sorry
