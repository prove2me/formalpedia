-- Prove2me | Theorems.Thm_finite_nonempty_has_maximal__p2m_9251ca56_2f13_4506_a97b_c72b0a41465a_a1
-- name    : finite_nonempty_has_maximal__p2m_9251ca56_2f13_4506_a97b_c72b0a41465a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:56:38.574123+00:00
-- url     : https://prove2.me/theorems/65e6eb57-b8db-462e-9942-6b7dc00b6b07
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element with no strictly larger element in that subset. The parent uses this for the finite partial order of simple graphs, with the subset consisting of drawable supergraphs of the given graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_nonempty_has_maximal__p2m_9251ca56_2f13_4506_a97b_c72b0a41465a_a1
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (hne : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b ≤ a := by sorry
