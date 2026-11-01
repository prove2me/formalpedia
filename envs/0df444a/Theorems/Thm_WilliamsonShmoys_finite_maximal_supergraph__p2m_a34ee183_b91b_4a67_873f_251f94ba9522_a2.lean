-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
-- name    : WilliamsonShmoys.finite_maximal_supergraph__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:17:52.132744+00:00
-- url     : https://prove2.me/theorems/7264886b-0cfb-4b76-9d54-df3461be3785
-- title:
--   Finite maximal supergraph for a predicate
-- statement:
--   For any predicate on simple graphs on a fixed finite linearly ordered vertex type, every graph satisfying the predicate has a supergraph satisfying it that is maximal under edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.finite_maximal_supergraph__p2m_a34ee183_b91b_4a67_873f_251f94ba9522_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      P H ∧
      (∀ J : SimpleGraph V,
        H.edgeSet ⊆ J.edgeSet →
        P J →
        J.edgeSet ⊆ H.edgeSet) := by
  sorry
