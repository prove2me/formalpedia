-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_set_progress_has_good_element__p2m_a6c61c44_359d_4d57_8094_2c2773f7c78b_a1
-- name    : WilliamsonShmoys.finite_set_progress_has_good_element__p2m_a6c61c44_359d_4d57_8094_2c2773f7c78b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:43:58.895838+00:00
-- url     : https://prove2.me/theorems/e90806bb-86fd-4257-bca7-3fba625400e0
-- title:
--   Finite strict progress reaches a good element
-- statement:
--   For a finite type, any nonempty set with a natural-number score contains a good element if every element that is not good admits a strictly higher-scoring element in the set. Choose a maximum-scoring element to prove the result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_set_progress_has_good_element__p2m_a6c61c44_359d_4d57_8094_2c2773f7c78b_a1 {α : Type} [Finite α] (s : Set α) (f : α → Nat) (good : α → Prop) (hs : s.Nonempty) (hstep : ∀ x ∈ s, ¬ good x → ∃ y ∈ s, f x < f y) : ∃ x ∈ s, good x := by sorry
