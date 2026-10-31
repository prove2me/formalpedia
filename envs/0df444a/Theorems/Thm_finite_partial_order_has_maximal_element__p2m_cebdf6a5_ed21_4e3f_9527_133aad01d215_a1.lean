-- Prove2me | Theorems.Thm_finite_partial_order_has_maximal_element__p2m_cebdf6a5_ed21_4e3f_9527_133aad01d215_a1
-- name    : finite_partial_order_has_maximal_element__p2m_cebdf6a5_ed21_4e3f_9527_133aad01d215_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:44:17.569978+00:00
-- url     : https://prove2.me/theorems/d1297ff7-bcb4-4e53-a20a-c13d7f55d923
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   In a finite partial order, every nonempty subset contains an element with no strictly greater member in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_partial_order_has_maximal_element__p2m_cebdf6a5_ed21_4e3f_9527_133aad01d215_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b ≤ a := by sorry
