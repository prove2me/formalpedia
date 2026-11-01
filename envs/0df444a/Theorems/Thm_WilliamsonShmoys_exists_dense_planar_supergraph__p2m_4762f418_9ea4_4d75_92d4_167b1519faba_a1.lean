-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_dense_planar_supergraph__p2m_4762f418_9ea4_4d75_92d4_167b1519faba_a1
-- name    : WilliamsonShmoys.exists_dense_planar_supergraph__p2m_4762f418_9ea4_4d75_92d4_167b1519faba_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:26:19.984256+00:00
-- url     : https://prove2.me/theorems/9339270d-9fc9-4b81-a23b-72e2e50fd8a3
-- title:
--   Dense drawable supergraph on the same vertex set
-- statement:
--   Any drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with at least 3|V|−6 edges. This allows the parent to use its maximality hypothesis to identify that supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_dense_planar_supergraph__p2m_4762f418_9ea4_4d75_92d4_167b1519faba_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  sorry
