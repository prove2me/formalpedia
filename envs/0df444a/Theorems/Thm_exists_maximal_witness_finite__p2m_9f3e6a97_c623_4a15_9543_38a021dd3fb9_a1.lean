-- Prove2me | Theorems.Thm_exists_maximal_witness_finite__p2m_9f3e6a97_c623_4a15_9543_38a021dd3fb9_a1
-- name    : exists_maximal_witness_finite__p2m_9f3e6a97_c623_4a15_9543_38a021dd3fb9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:03:31.815218+00:00
-- url     : https://prove2.me/theorems/6b43ba92-59f4-47ec-b6a0-8b33a6f9aef1
-- title:
--   A nonempty predicate in a finite partial order has a maximal witness
-- statement:
--   Any nonempty predicate on a finite partially ordered type has a witness that has no distinct predicate-satisfying extension above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_witness_finite__p2m_9f3e6a97_c623_4a15_9543_38a021dd3fb9_a1
    {α : Type} [Finite α] [PartialOrder α] (Q : α → Prop)
    (hQ : ∃ x, Q x) :
    ∃ x, Q x ∧ ∀ y, Q y → x ≤ y → y = x := by sorry
