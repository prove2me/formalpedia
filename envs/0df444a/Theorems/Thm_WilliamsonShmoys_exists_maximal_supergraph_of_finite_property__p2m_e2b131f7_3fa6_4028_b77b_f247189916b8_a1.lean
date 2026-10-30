-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_property__p2m_e2b131f7_3fa6_4028_b77b_f247189916b8_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite_property__p2m_e2b131f7_3fa6_4028_b77b_f247189916b8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:20:36.085268+00:00
-- url     : https://prove2.me/theorems/d2eb82da-0a74-4ed2-b0cc-73d83d187123
-- title:
--   Finite maximal supergraph for a hereditary property
-- statement:
--   For a finite ordered vertex type, any graph satisfying a property that is preserved under taking subgraphs has a supergraph that satisfies the property and is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite_property__p2m_e2b131f7_3fa6_4028_b77b_f247189916b8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ P M ∧ ∀ N : SimpleGraph V, M ≤ N → P N → N ≤ M := by
  sorry
