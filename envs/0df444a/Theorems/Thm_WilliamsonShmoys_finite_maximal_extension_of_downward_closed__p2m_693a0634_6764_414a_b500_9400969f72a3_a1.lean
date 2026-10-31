-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension_of_downward_closed__p2m_693a0634_6764_414a_b500_9400969f72a3_a1
-- name    : WilliamsonShmoys.finite_maximal_extension_of_downward_closed__p2m_693a0634_6764_414a_b500_9400969f72a3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:44:35.838518+00:00
-- url     : https://prove2.me/theorems/308e57e3-f473-4c2d-add3-2b2c00ce915b
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   For a finite vertex type, any downward-closed graph property satisfied by N has a supergraph Q satisfying that property such that every further supergraph satisfying it has the same edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension_of_downward_closed__p2m_693a0634_6764_414a_b500_9400969f72a3_a1 {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V → Prop) (N : SimpleGraph V) (hPN : P N) (hDown : ∀ G H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet → P H → P G) : ∃ Q : SimpleGraph V, N.edgeSet ⊆ Q.edgeSet ∧ P Q ∧ ∀ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet → P R → R.edgeSet = Q.edgeSet := by sorry
