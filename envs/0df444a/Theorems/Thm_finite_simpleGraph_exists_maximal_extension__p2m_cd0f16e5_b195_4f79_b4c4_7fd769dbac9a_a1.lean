-- Prove2me | Theorems.Thm_finite_simpleGraph_exists_maximal_extension__p2m_cd0f16e5_b195_4f79_b4c4_7fd769dbac9a_a1
-- name    : finite_simpleGraph_exists_maximal_extension__p2m_cd0f16e5_b195_4f79_b4c4_7fd769dbac9a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:31:09.432715+00:00
-- url     : https://prove2.me/theorems/8d5ed552-2ffc-4551-a665-48082a15cce3
-- title:
--   Finite maximal extension for an edge-hereditary graph property
-- statement:
--   For a finite vertex type, any graph satisfying a property that is preserved when edges are removed has a supergraph satisfying that property which is maximal under edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_simpleGraph_exists_maximal_extension__p2m_cd0f16e5_b195_4f79_b4c4_7fd769dbac9a_a1 {V : Type} [Fintype V] (M : SimpleGraph V) (P : SimpleGraph V → Prop) (hmono : ∀ {A B : SimpleGraph V}, B.edgeSet ⊆ A.edgeSet → P A → P B) (hM : P M) : ∃ N : SimpleGraph V, M.edgeSet ⊆ N.edgeSet ∧ P N ∧ ∀ Q : SimpleGraph V, N.edgeSet ⊆ Q.edgeSet → P Q → Q.edgeSet = N.edgeSet := by sorry
