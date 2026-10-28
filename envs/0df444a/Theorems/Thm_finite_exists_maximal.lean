-- Prove2me | Theorems.Thm_finite_exists_maximal
-- name    : finite_exists_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:04:00.319419+00:00
-- url     : https://prove2.me/theorems/53f4f870-506e-47d5-b1e3-6417af6155fa
-- title:
--   A nonempty subset of a finite preorder has a maximal element
-- statement:
--   For a finite type equipped with a reflexive and transitive relation, every nonempty predicate-defined subset contains an element that is maximal within that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_exists_maximal {α : Type} [Finite α] (P : α → Prop) (R : α → α → Prop) (hRrefl : ∀ x, R x x) (hRtrans : ∀ ⦃x y z⦄, R x y → R y z → R x z) (hP : ∃ x, P x) : ∃ x, P x ∧ ∀ y, P y → R x y → R y x := by sorry
