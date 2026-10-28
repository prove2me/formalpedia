-- Prove2me | Theorems.Thm_finite_predicate_has_maximal_extension
-- name    : finite_predicate_has_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:19:35.447999+00:00
-- url     : https://prove2.me/theorems/b7cfb662-2a2f-4a77-a5cf-44c78cb4531b
-- title:
--   A finite preorder has maximal predicate-satisfying extensions
-- statement:
--   For a reflexive and transitive relation on a finite type, every element satisfying a predicate has a predicate-satisfying extension above it that is maximal among predicate-satisfying extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_predicate_has_maximal_extension
    {α : Type} [Fintype α]
    (r : α → α → Prop)
    (hrefl : ∀ a, r a a)
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (P : α → Prop)
    (a : α) (ha : P a) :
    ∃ b, P b ∧ r a b ∧ ∀ c, P c → r b c → r c b := by sorry
