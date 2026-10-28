-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_property_extension_maximal__p2m_af21b660_e263_41f3_a209_fea21d5ace1b_a1
-- name    : WilliamsonShmoys.finite_property_extension_maximal__p2m_af21b660_e263_41f3_a209_fea21d5ace1b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:40:52.231787+00:00
-- url     : https://prove2.me/theorems/b627b66b-7038-44ac-a9b3-e51226961fdb
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For a finite vertex type, every graph satisfying a property has a supergraph satisfying the same property that is maximal under edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_property_extension_maximal__p2m_af21b660_e263_41f3_a209_fea21d5ace1b_a1
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ M : SimpleGraph V,
      K.edgeSet ⊆ M.edgeSet ∧
      P M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊆ N.edgeSet →
        P N →
        N.edgeSet ⊆ M.edgeSet := by sorry
