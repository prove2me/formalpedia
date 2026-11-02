-- Prove2me | Theorems.Thm_exists_maximal_element_above_finite__p2m_ff2c7fc5_47bb_41b0_9771_afa052fe6028_a1
-- name    : exists_maximal_element_above_finite__p2m_ff2c7fc5_47bb_41b0_9771_afa052fe6028_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:50:11.649316+00:00
-- url     : https://prove2.me/theorems/bd75be51-d4f4-426c-b5ea-1a61499f9821
-- title:
--   A finite poset has a maximal element above a given member
-- statement:
--   In a finite partially ordered type, any property holding of a has a maximal member above a among the elements satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem exists_maximal_element_above_finite__p2m_ff2c7fc5_47bb_41b0_9771_afa052fe6028_a1
    {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c = b := by sorry
