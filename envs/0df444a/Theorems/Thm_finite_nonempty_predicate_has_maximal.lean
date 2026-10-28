-- Prove2me | Theorems.Thm_finite_nonempty_predicate_has_maximal
-- name    : finite_nonempty_predicate_has_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:17:09.767273+00:00
-- url     : https://prove2.me/theorems/f24230c0-7d36-4ebb-be1a-fc010b0412c1
-- title:
--   A nonempty predicate on a finite partial order has a maximal element
-- statement:
--   Every nonempty decidable subset of a finite partially ordered type contains an element with no strictly larger member in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_nonempty_predicate_has_maximal
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) [DecidablePred P]
    (hP : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → x ≤ y → y ≤ x := by
  sorry
