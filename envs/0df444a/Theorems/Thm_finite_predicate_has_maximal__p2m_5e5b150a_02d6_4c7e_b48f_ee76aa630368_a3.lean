-- Prove2me | Theorems.Thm_finite_predicate_has_maximal__p2m_5e5b150a_02d6_4c7e_b48f_ee76aa630368_a3
-- name    : finite_predicate_has_maximal__p2m_5e5b150a_02d6_4c7e_b48f_ee76aa630368_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:18:58.019538+00:00
-- url     : https://prove2.me/theorems/490c4079-511d-4691-b289-14e9c481d9f2
-- title:
--   A finite predicate has a maximal element
-- statement:
--   Every nonempty predicate on a finite partially ordered type contains an element that has no strictly larger element within the predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_predicate_has_maximal__p2m_5e5b150a_02d6_4c7e_b48f_ee76aa630368_a3
    {α : Type} [Fintype α] [PartialOrder α] (p : α → Prop)
    (hp : ∃ x, p x) :
    ∃ m, p m ∧ ∀ x, p x → m ≤ x → x ≤ m := by
  sorry
