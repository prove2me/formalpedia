-- Prove2me | Theorems.Thm_finite_nonempty_set_has_maximal__p2m_728754b2_3360_4212_89f5_97b877a982a4_a1
-- name    : finite_nonempty_set_has_maximal__p2m_728754b2_3360_4212_89f5_97b877a982a4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:03.635998+00:00
-- url     : https://prove2.me/theorems/5e2c5a45-e6f9-4183-a9c1-09b77bcaa834
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element with no strictly larger element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_nonempty_set_has_maximal__p2m_728754b2_3360_4212_89f5_97b877a982a4_a1 {α : Type} [Finite α] [PartialOrder α] (s : Set α) (hne : s.Nonempty) : ∃ a ∈ s, ∀ b ∈ s, a ≤ b → b ≤ a := by sorry
