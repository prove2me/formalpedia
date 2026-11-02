-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_hereditary_maximal__p2m_f28d325a_badb_43f7_b5e1_caa5a9a8c825_a2
-- name    : WilliamsonShmoys.finite_hereditary_maximal__p2m_f28d325a_badb_43f7_b5e1_caa5a9a8c825_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:03:23.398031+00:00
-- url     : https://prove2.me/theorems/6789a3e1-218f-4c0d-b63c-878808cfead0
-- title:
--   Finite hereditary properties have maximal extensions
-- statement:
--   On a finite vertex type, every graph satisfying a subgraph-closed property has a supergraph maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_hereditary_maximal__p2m_f28d325a_badb_43f7_b5e1_caa5a9a8c825_a2
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hG : P G)
    (hdown : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
        ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  sorry
