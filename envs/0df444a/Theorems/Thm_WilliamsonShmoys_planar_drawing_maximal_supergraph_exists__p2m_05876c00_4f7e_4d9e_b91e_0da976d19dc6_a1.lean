-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists__p2m_05876c00_4f7e_4d9e_b91e_0da976d19dc6_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_05876c00_4f7e_4d9e_b91e_0da976d19dc6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:52:03.277133+00:00
-- url     : https://prove2.me/theorems/7757e537-42c8-4461-8d38-eae034a917fc
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has an inclusion-maximal drawable supergraph on the same vertex type. The result follows by maximizing the edge count over the finite family of drawable supergraphs containing the input; any proper extension would add an edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_05876c00_4f7e_4d9e_b91e_0da976d19dc6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      (∀ u v, G.Adj u v → L.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V,
        (∀ u v, L.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        ∀ u v, K.Adj u v → L.Adj u v := by sorry
