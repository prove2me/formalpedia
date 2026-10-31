-- Prove2me | Theorems.Thm_finite_nonempty_subset_has_maximal__p2m_f12881bc_f698_449c_9421_69b4df3ce3de_a1
-- name    : finite_nonempty_subset_has_maximal__p2m_f12881bc_f698_449c_9421_69b4df3ce3de_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:04:45.954372+00:00
-- url     : https://prove2.me/theorems/ce231f40-db8a-4be6-a426-2d168df6d160
-- title:
--   Maximal element in a finite nonempty subset
-- statement:
--   For any finite type equipped with a reflexive, transitive, antisymmetric relation, every nonempty subset contains an element with no strictly larger related element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem finite_nonempty_subset_has_maximal__p2m_f12881bc_f698_449c_9421_69b4df3ce3de_a1 {α : Type} [Fintype α] (r : α → α → Prop) (hrefl : ∀ a, r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c) (hanti : ∀ {a b}, r a b → r b a → a = b) (S : Set α) (hS : S.Nonempty) : ∃ a, S a ∧ ∀ b, S b → r a b → r b a := by sorry
