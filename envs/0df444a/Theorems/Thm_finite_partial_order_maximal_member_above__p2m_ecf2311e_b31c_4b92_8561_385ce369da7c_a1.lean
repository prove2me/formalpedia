-- Prove2me | Theorems.Thm_finite_partial_order_maximal_member_above__p2m_ecf2311e_b31c_4b92_8561_385ce369da7c_a1
-- name    : finite_partial_order_maximal_member_above__p2m_ecf2311e_b31c_4b92_8561_385ce369da7c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:47:01.781591+00:00
-- url     : https://prove2.me/theorems/4af77e3e-5e92-4dc0-9c2e-8f182405a83c
-- title:
--   A finite predicate has a maximal member above each of its members
-- statement:
--   In a finite partially ordered type, every member of any predicate lies below a member of that predicate that is maximal within the predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_partial_order_maximal_member_above__p2m_ecf2311e_b31c_4b92_8561_385ce369da7c_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) {a : α} (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, P c → b ≤ c → c = b := by sorry
