-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite__p2m_6da47f0d_a7ea_48c9_976b_3e23d82be4ec_a2
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_6da47f0d_a7ea_48c9_976b_3e23d82be4ec_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:44:33.32049+00:00
-- url     : https://prove2.me/theorems/fcd41b43-10e5-45f3-91a3-1ff688cd58ad
-- title:
--   Maximal member of a hereditary graph family
-- statement:
--   For any hereditary property of graphs on a finite ordered vertex type, each graph satisfying the property has a supergraph satisfying it that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_6da47f0d_a7ea_48c9_976b_3e23d82be4ec_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hH : P H)
    (hmono : ∀ {G K : SimpleGraph V}, G ≤ K → P K → P G) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
        ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by
  sorry
