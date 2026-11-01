-- Prove2me | Theorems.Thm_finite_maximal_element__p2m_7264886b_0cfb_4b76_9d54_df3461be3785_a2
-- name    : finite_maximal_element__p2m_7264886b_0cfb_4b76_9d54_df3461be3785_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:18.297882+00:00
-- url     : https://prove2.me/theorems/0f6ce041-7cfe-447c-8278-c776211aa935
-- title:
--   Maximal element in a finite partially ordered set
-- statement:
--   Every nonempty subset of a finite partially ordered type has an element with no strictly greater element in that subset. This supplies maximality for the feasible family of supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_maximal_element__p2m_7264886b_0cfb_4b76_9d54_df3461be3785_a2
    {α : Type} [Fintype α] [PartialOrder α]
    (S : Set α) (hS : S.Nonempty) :
    ∃ a, a ∈ S ∧ ∀ b, b ∈ S → a ≤ b → b ≤ a := by
  sorry
