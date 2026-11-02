-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph_of_hereditary_property__p2m_813de8ea_e58e_48bb_807f_43145eda7132_a1
-- name    : WilliamsonShmoys.finite_maximal_supergraph_of_hereditary_property__p2m_813de8ea_e58e_48bb_807f_43145eda7132_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:24:07.703923+00:00
-- url     : https://prove2.me/theorems/feaaaf4b-51e3-4891-91fb-928579619597
-- title:
--   Finite hereditary graph properties have maximal extensions
-- statement:
--   On a finite vertex type, every graph satisfying a subgraph-closed property has a supergraph satisfying that property which is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_supergraph_of_hereditary_property__p2m_813de8ea_e58e_48bb_807f_43145eda7132_a1 {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) (hclosed : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A) : ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by sorry
