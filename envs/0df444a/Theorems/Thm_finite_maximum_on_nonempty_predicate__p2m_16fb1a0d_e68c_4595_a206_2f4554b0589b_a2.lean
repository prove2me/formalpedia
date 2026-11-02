-- Prove2me | Theorems.Thm_finite_maximum_on_nonempty_predicate__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a2
-- name    : finite_maximum_on_nonempty_predicate__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:22:05.315069+00:00
-- url     : https://prove2.me/theorems/0e7a07f1-3c50-4c43-949b-335424bf835f
-- title:
--   A natural-valued function attains a maximum on a nonempty finite predicate
-- statement:
--   On a finite type, every natural-valued function attains a maximum among the elements satisfying an inhabited predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem finite_maximum_on_nonempty_predicate__p2m_16fb1a0d_e68c_4595_a206_2f4554b0589b_a2
    {α : Type} [Fintype α] (P : α → Prop) (f : α → Nat)
    (hP : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → f y ≤ f x := by sorry
