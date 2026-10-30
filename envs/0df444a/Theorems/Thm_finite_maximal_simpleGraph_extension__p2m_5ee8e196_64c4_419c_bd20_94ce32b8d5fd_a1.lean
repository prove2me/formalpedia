-- Prove2me | Theorems.Thm_finite_maximal_simpleGraph_extension__p2m_5ee8e196_64c4_419c_bd20_94ce32b8d5fd_a1
-- name    : finite_maximal_simpleGraph_extension__p2m_5ee8e196_64c4_419c_bd20_94ce32b8d5fd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:28:41.238241+00:00
-- url     : https://prove2.me/theorems/f3c829e6-6472-40b7-9154-27454eec289f
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   For a finite vertex type, every graph satisfying a predicate has an extension satisfying that predicate that is maximal under edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_maximal_simpleGraph_extension__p2m_5ee8e196_64c4_419c_bd20_94ce32b8d5fd_a1 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K) : ∃ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet ∧ P L ∧ ∀ M : SimpleGraph V, L.edgeSet ⊆ M.edgeSet → P M → M.edgeSet = L.edgeSet := by sorry
