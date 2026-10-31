-- Prove2me | Theorems.Thm_finite_exists_maximal__p2m_3cbfa21b_87e9_46ce_9a05_e9f44cd63dc5_a1
-- name    : finite_exists_maximal__p2m_3cbfa21b_87e9_46ce_9a05_e9f44cd63dc5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:59:32.720859+00:00
-- url     : https://prove2.me/theorems/63e7f4ed-cc10-4459-89d7-e1b44a61fe20
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   Every nonempty subset of a finite partial order contains an element with no strictly larger element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_exists_maximal__p2m_3cbfa21b_87e9_46ce_9a05_e9f44cd63dc5_a1
    {α : Type} [Fintype α] [PartialOrder α] (S : Set α) (hne : S.Nonempty) :
    ∃ a ∈ S, ∀ b, a ≤ b → b ∈ S → b ≤ a := by
  sorry
