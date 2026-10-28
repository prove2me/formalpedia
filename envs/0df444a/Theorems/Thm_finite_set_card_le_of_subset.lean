-- Prove2me | Theorems.Thm_finite_set_card_le_of_subset
-- name    : finite_set_card_le_of_subset
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:14:24.883644+00:00
-- url     : https://prove2.me/theorems/2411b341-1a39-4444-b7ea-75c5c6bfdce1
-- title:
--   Finite-set inclusion and reverse cardinality imply equality
-- statement:
--   If finite sets A and B satisfy A ⊆ B and B has cardinality at most that of A, then A = B.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_set_card_le_of_subset
    {α : Type} [Fintype α]
    (A B : Set α)
    (hA : A.Finite) (hB : B.Finite)
    (hAB : A ⊆ B)
    (hcard : B.ncard ≤ A.ncard) :
    A = B := by
  sorry
