-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_property_maximal_extension__p2m_aafbf6a1_f3ed_41ff_93d8_51adc42299ad_a1
-- name    : WilliamsonShmoys.finite_graph_property_maximal_extension__p2m_aafbf6a1_f3ed_41ff_93d8_51adc42299ad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:36:58.703206+00:00
-- url     : https://prove2.me/theorems/924161ef-19fb-41d1-9b0d-c817a0dc77d2
-- title:
--   Finite graph property maximal extension
-- statement:
--   For any property of simple graphs on a fixed finite vertex type, every graph satisfying that property has a supergraph satisfying it that is maximal under inclusion among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_property_maximal_extension__p2m_aafbf6a1_f3ed_41ff_93d8_51adc42299ad_a1 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) : ∃ M : SimpleGraph V, G ≤ M ∧ P M ∧ ∀ N : SimpleGraph V, M ≤ N → P N → N = M := by sorry
