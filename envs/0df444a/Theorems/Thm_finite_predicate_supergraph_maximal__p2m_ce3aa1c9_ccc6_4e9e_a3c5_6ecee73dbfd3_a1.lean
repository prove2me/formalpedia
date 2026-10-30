-- Prove2me | Theorems.Thm_finite_predicate_supergraph_maximal__p2m_ce3aa1c9_ccc6_4e9e_a3c5_6ecee73dbfd3_a1
-- name    : finite_predicate_supergraph_maximal__p2m_ce3aa1c9_ccc6_4e9e_a3c5_6ecee73dbfd3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:45:37.74239+00:00
-- url     : https://prove2.me/theorems/9601ee75-4f1c-4f3c-9a26-b888e9dcc3ab
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   For any property of simple graphs on a finite vertex type, every graph satisfying the property has a supergraph satisfying it that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem finite_predicate_supergraph_maximal__p2m_ce3aa1c9_ccc6_4e9e_a3c5_6ecee73dbfd3_a1 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) : ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧ (∀ L : SimpleGraph V, K ≤ L → P L → L = K) := by sorry
