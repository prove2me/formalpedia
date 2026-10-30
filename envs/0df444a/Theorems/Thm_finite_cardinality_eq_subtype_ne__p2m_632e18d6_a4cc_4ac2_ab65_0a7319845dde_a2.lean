-- Prove2me | Theorems.Thm_finite_cardinality_eq_subtype_ne__p2m_632e18d6_a4cc_4ac2_ab65_0a7319845dde_a2
-- name    : finite_cardinality_eq_subtype_ne__p2m_632e18d6_a4cc_4ac2_ab65_0a7319845dde_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:39:28.962627+00:00
-- url     : https://prove2.me/theorems/eb24eb1f-7a71-47bd-a51e-3e411d165af1
-- title:
--   Cardinality after removing one element
-- statement:
--   A finite type’s cardinality is one more than the cardinality of the subtype excluding any chosen element.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Data.Set.Card

theorem finite_cardinality_eq_subtype_ne__p2m_632e18d6_a4cc_4ac2_ab65_0a7319845dde_a2
    {α : Type} [Fintype α] (a : α) :
    Nat.card α = Nat.card {x : α // x ≠ a} + 1 := by sorry
