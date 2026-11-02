-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_predicate_has_maximal_extension__p2m_90a1d3cf_69db_4650_95dd_fb78166e4c20_a1
-- name    : WilliamsonShmoys.finite_predicate_has_maximal_extension__p2m_90a1d3cf_69db_4650_95dd_fb78166e4c20_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:48:45.966681+00:00
-- url     : https://prove2.me/theorems/3be92c02-acbf-4899-85c0-d3e4dc6170c4
-- title:
--   A nonempty predicate on a finite partial order has a maximal member
-- statement:
--   Every nonempty predicate on a finite partially ordered type contains an element that has no strictly greater member in that predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_predicate_has_maximal_extension__p2m_90a1d3cf_69db_4650_95dd_fb78166e4c20_a1
    {α : Type} [PartialOrder α] [Finite α]
    (S : α → Prop) (a : α) (ha : S a) :
    ∃ b, S b ∧ ∀ c, b ≤ c → S c → c = b := by sorry
