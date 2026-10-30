-- Prove2me | Theorems.Thm_finite_exists_max_predicate__p2m_caf8a86e_ba48_4365_a372_a27064dc0c60_a1
-- name    : finite_exists_max_predicate__p2m_caf8a86e_ba48_4365_a372_a27064dc0c60_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:12.749154+00:00
-- url     : https://prove2.me/theorems/70dda6a9-2ea3-437f-b088-5ef8740e3ffa
-- title:
--   Maximum of a predicate on a finite type
-- statement:
--   On a finite type, any nonempty predicate class contains an element maximizing a natural-valued function.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_exists_max_predicate__p2m_caf8a86e_ba48_4365_a372_a27064dc0c60_a1
    {α : Type} [Finite α] (P : α → Prop) (f : α → Nat)
    (hP : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by sorry
