-- Prove2me | Theorems.Thm_exists_maximal_finite_preorder__p2m_7dd72d83_34f6_4f08_ba9a_4bb87d91a259_a1
-- name    : exists_maximal_finite_preorder__p2m_7dd72d83_34f6_4f08_ba9a_4bb87d91a259_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:58:48.515131+00:00
-- url     : https://prove2.me/theorems/8d5187fb-19d2-476e-86b0-dcba5b4406c1
-- title:
--   Maximal element in a finite preorder subset
-- statement:
--   For a finite type with a reflexive, transitive relation, every nonempty subset contains an element maximal up to equivalence under that relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_finite_preorder__p2m_7dd72d83_34f6_4f08_ba9a_4bb87d91a259_a1 {α : Type} [Finite α] (R : α → α → Prop) (P : α → Prop) (hrefl : ∀ a, R a a) (htrans : ∀ a b c, R a b → R b c → R a c) (hne : ∃ a, P a) : ∃ a, P a ∧ ∀ b, P b → R a b → R b a := by sorry
