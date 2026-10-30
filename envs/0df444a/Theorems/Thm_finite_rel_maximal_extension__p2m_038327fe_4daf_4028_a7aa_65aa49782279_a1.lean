-- Prove2me | Theorems.Thm_finite_rel_maximal_extension__p2m_038327fe_4daf_4028_a7aa_65aa49782279_a1
-- name    : finite_rel_maximal_extension__p2m_038327fe_4daf_4028_a7aa_65aa49782279_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T20:56:01.534163+00:00
-- url     : https://prove2.me/theorems/038e24c3-977e-4ae1-ac80-fa90e8eb17bc
-- title:
--   Maximal extension in a finite partial order
-- statement:
--   In a finite partial order, every predicate-satisfying element has a predicate-satisfying maximal extension above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_rel_maximal_extension__p2m_038327fe_4daf_4028_a7aa_65aa49782279_a1 {α : Type} [Finite α] (r : α → α → Prop) (hrefl : ∀ a, r a a) (htrans : ∀ a b c, r a b → r b c → r a c) (hantisymm : ∀ a b, r a b → r b a → a = b) (Q : α → Prop) (x : α) (hx : Q x) : ∃ y, Q y ∧ r x y ∧ ∀ z, Q z → r y z → r z y := by sorry
