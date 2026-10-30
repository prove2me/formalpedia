-- Prove2me | Theorems.Thm_finite_maximal_by_measure__p2m_27628b41_9b86_421c_a9af_b79318367974_a2
-- name    : finite_maximal_by_measure__p2m_27628b41_9b86_421c_a9af_b79318367974_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:43:18.617274+00:00
-- url     : https://prove2.me/theorems/40f92af2-b652-416e-a759-ad573a97be44
-- title:
--   A finite admissible family has a maximal element under a strictly increasing measure
-- statement:
--   In a nonempty family on a finite type, if every distinct admissible extension strictly increases a natural-number measure, some family member has no distinct admissible extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem finite_maximal_by_measure__p2m_27628b41_9b86_421c_a9af_b79318367974_a2 {α : Type} [Fintype α] (S : Set α) (hS : S.Nonempty) (μ : α → Nat) (R : α → α → Prop) (hinc : ∀ a b, a ∈ S → b ∈ S → R a b → a ≠ b → μ a < μ b) : ∃ a, a ∈ S ∧ ∀ b, b ∈ S → R a b → b = a := by sorry
