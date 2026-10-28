-- Prove2me | Theorems.Thm_finite_maximal_element
-- name    : finite_maximal_element
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:53:36.642524+00:00
-- url     : https://prove2.me/theorems/c0f67fba-297f-4b47-88d5-68060a63f421
-- title:
--   Maximum rank in a finite feasible family
-- statement:
--   In a finite type, a nonempty feasible family containing a has a maximum-rank member that remains related to a.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_maximal_element
    {α : Type} [Fintype α]
    (P : α → Prop) (R : α → α → Prop) (rank : α → Nat) (a : α)
    (ha : P a)
    (hbase : ∀ b, P b → R a b) :
    ∃ b, P b ∧ R a b ∧ ∀ c, P c → rank c ≤ rank b := by sorry
