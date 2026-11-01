-- Prove2me | Theorems.Thm_finite_partial_order_has_maximal_above__p2m_b64ec28e_2554_405c_95cb_8078e84c56ed_a1
-- name    : finite_partial_order_has_maximal_above__p2m_b64ec28e_2554_405c_95cb_8078e84c56ed_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:39:07.890195+00:00
-- url     : https://prove2.me/theorems/dbf886ac-5640-48b2-9eeb-ab7f14638c7a
-- title:
--   A finite partial order has a maximal element above each element
-- statement:
--   In a finite partially ordered type, every element lies below a maximal element.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_partial_order_has_maximal_above__p2m_b64ec28e_2554_405c_95cb_8078e84c56ed_a1
    {α : Type} [PartialOrder α] [Finite α] (a : α) :
    ∃ b : α, a ≤ b ∧ ∀ c : α, b ≤ c → c = b := by sorry
