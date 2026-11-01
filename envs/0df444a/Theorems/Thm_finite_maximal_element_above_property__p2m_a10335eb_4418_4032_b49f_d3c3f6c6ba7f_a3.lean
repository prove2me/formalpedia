-- Prove2me | Theorems.Thm_finite_maximal_element_above_property__p2m_a10335eb_4418_4032_b49f_d3c3f6c6ba7f_a3
-- name    : finite_maximal_element_above_property__p2m_a10335eb_4418_4032_b49f_d3c3f6c6ba7f_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:49:56.903+00:00
-- url     : https://prove2.me/theorems/7d2b4361-bf48-4c0c-bfed-f5868e634964
-- title:
--   A finite partial order has a maximal satisfying element above a witness
-- statement:
--   In a finite partially ordered type, any element satisfying a predicate lies below a maximal element that also satisfies the predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_maximal_element_above_property__p2m_a10335eb_4418_4032_b49f_d3c3f6c6ba7f_a3
    {α : Type} [Fintype α] [PartialOrder α]
    (Q : α → Prop) (a : α) (ha : Q a) :
    ∃ b : α, a ≤ b ∧ Q b ∧ ∀ c : α, b ≤ c → Q c → c = b := by sorry
