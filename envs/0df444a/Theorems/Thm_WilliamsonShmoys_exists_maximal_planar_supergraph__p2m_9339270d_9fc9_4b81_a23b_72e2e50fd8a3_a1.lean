-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_9339270d_9fc9_4b81_a23b_72e2e50fd8a3_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9339270d_9fc9_4b81_a23b_72e2e50fd8a3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:34:35.987905+00:00
-- url     : https://prove2.me/theorems/4be4105c-73cc-4342-be68-e4f6ac421142
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has an inclusion-maximal drawable supergraph on that same vertex type. The finite family of simple graphs contains at least the original graph; choose a drawable extension maximizing its number of edges. Any drawable extension of that choice must have the same edge set, hence be equal to it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9339270d_9fc9_4b81_a23b_72e2e50fd8a3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        (∀ u v, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  sorry
