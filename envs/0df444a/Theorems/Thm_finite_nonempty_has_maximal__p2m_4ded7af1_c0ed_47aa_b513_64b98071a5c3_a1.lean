-- Prove2me | Theorems.Thm_finite_nonempty_has_maximal__p2m_4ded7af1_c0ed_47aa_b513_64b98071a5c3_a1
-- name    : finite_nonempty_has_maximal__p2m_4ded7af1_c0ed_47aa_b513_64b98071a5c3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:57:44.053917+00:00
-- url     : https://prove2.me/theorems/31af88cd-1382-4400-877e-4ebb808fadf8
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element for which any subset element above it is also below it, and hence is equal to it by antisymmetry.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_nonempty_has_maximal__p2m_4ded7af1_c0ed_47aa_b513_64b98071a5c3_a1 {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → a ≤ b → b ≤ a := by sorry
