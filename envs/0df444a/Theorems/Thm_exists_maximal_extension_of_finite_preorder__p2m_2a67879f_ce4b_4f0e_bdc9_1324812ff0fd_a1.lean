-- Prove2me | Theorems.Thm_exists_maximal_extension_of_finite_preorder__p2m_2a67879f_ce4b_4f0e_bdc9_1324812ff0fd_a1
-- name    : exists_maximal_extension_of_finite_preorder__p2m_2a67879f_ce4b_4f0e_bdc9_1324812ff0fd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:32:19.997011+00:00
-- url     : https://prove2.me/theorems/89f43dad-f738-40ea-8784-45344bc2dcf0
-- title:
--   Predicate-satisfying maximal extensions in finite preorders
-- statement:
--   In a finite type with a reflexive and transitive relation, every element satisfying a predicate has a predicate-satisfying extension that is maximal among such extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_extension_of_finite_preorder__p2m_2a67879f_ce4b_4f0e_bdc9_1324812ff0fd_a1 {α : Type} [Finite α] (r : α → α → Prop) (hrefl : ∀ a, r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c) (P : α → Prop) (a : α) (ha : P a) : ∃ b, r a b ∧ P b ∧ ∀ c, r b c → P c → r c b := by sorry
