-- Prove2me | Theorems.Thm_finite_predicate_has_maximum__p2m_732ef142_c02d_434e_9b88_adbee85d4bda_a1
-- name    : finite_predicate_has_maximum__p2m_732ef142_c02d_434e_9b88_adbee85d4bda_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:39:59.565786+00:00
-- url     : https://prove2.me/theorems/68752a50-8bfe-4618-9db6-34a6b9e0c244
-- title:
--   A Nat-valued function has a maximum on a nonempty finite predicate
-- statement:
--   For any finite type, predicate, and Nat-valued function, if some element satisfies the predicate, then a predicate-satisfying element maximizes the function over all predicate-satisfying elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_predicate_has_maximum__p2m_732ef142_c02d_434e_9b88_adbee85d4bda_a1 {α : Type} [Fintype α] (P : α → Prop) (f : α → Nat) (hP : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → f b ≤ f a := by sorry
