-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_hereditary_maximal_supergraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a2
-- name    : WilliamsonShmoys.finite_hereditary_maximal_supergraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:39:21.735344+00:00
-- url     : https://prove2.me/theorems/d5b8f321-118e-45f3-bc9a-bdeab3f4bbb9
-- title:
--   Finite maximal extension for a hereditary graph property
-- statement:
--   For a finite vertex type, every graph satisfying a property inherited by subgraphs has a maximal supergraph satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_hereditary_maximal_supergraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a2 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (hP : ∀ ⦃G H : SimpleGraph V⦄, G ≤ H → P H → P G) (K : SimpleGraph V) (hK : P K) : ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧ ∀ G : SimpleGraph V, H ≤ G → P G → G ≤ H := by sorry
