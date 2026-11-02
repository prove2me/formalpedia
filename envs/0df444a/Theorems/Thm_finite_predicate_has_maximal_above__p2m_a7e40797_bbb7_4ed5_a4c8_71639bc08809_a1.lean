-- Prove2me | Theorems.Thm_finite_predicate_has_maximal_above__p2m_a7e40797_bbb7_4ed5_a4c8_71639bc08809_a1
-- name    : finite_predicate_has_maximal_above__p2m_a7e40797_bbb7_4ed5_a4c8_71639bc08809_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:48:20.768296+00:00
-- url     : https://prove2.me/theorems/10dba006-7db4-4b77-87ac-ad44adb343b6
-- title:
--   Maximal satisfying element above a given element in a finite preorder
-- statement:
--   For a predicate on a finite preorder, every satisfying element lies below a satisfying element that has no strictly greater satisfying element.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_predicate_has_maximal_above__p2m_a7e40797_bbb7_4ed5_a4c8_71639bc08809_a1
    {α : Type} [Preorder α] [Finite α]
    (S : α → Prop) (x : α) (hx : S x) :
    ∃ y, S y ∧ x ≤ y ∧ ∀ z, S z → y ≤ z → z ≤ y := by sorry
