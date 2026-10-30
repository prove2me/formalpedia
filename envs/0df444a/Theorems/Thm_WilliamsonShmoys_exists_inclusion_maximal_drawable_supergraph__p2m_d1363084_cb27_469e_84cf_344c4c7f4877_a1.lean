-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_supergraph__p2m_d1363084_cb27_469e_84cf_344c4c7f4877_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_d1363084_cb27_469e_84cf_344c4c7f4877_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:03:54.042889+00:00
-- url     : https://prove2.me/theorems/ebc26ecc-dfea-4863-8cab-260c69e4997d
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex set that is inclusion-maximal among drawable supergraphs of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_d1363084_cb27_469e_84cf_344c4c7f4877_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ H : SimpleGraph V,
        G ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → K ≤ H → H ≤ K) := by sorry
