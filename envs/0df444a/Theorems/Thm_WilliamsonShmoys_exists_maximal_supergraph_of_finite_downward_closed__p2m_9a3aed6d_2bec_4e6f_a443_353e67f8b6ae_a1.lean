-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_downward_closed__p2m_9a3aed6d_2bec_4e6f_a443_353e67f8b6ae_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite_downward_closed__p2m_9a3aed6d_2bec_4e6f_a443_353e67f8b6ae_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:41.585957+00:00
-- url     : https://prove2.me/theorems/2212fb5a-3b8b-4ff4-b66b-e1a858c8b349
-- title:
--   Maximal extension for a finite downward-closed graph property
-- statement:
--   For a finite vertex type, any graph satisfying a property that is preserved when edges are removed has an inclusion-maximal supergraph satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite_downward_closed__p2m_9a3aed6d_2bec_4e6f_a443_353e67f8b6ae_a1 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A) (G : SimpleGraph V) (hG : P G) : ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by sorry
