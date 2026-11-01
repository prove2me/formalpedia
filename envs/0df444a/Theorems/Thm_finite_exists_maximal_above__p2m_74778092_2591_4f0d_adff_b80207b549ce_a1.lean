-- Prove2me | Theorems.Thm_finite_exists_maximal_above__p2m_74778092_2591_4f0d_adff_b80207b549ce_a1
-- name    : finite_exists_maximal_above__p2m_74778092_2591_4f0d_adff_b80207b549ce_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:37:17.305547+00:00
-- url     : https://prove2.me/theorems/3b3e3456-4a88-4058-bc70-f203b9e7589b
-- title:
--   A maximal predicate element above a given point in a finite partial order
-- statement:
--   In a finite partial order, every element satisfying a predicate lies below a predicate-satisfying element that is maximal among predicate-satisfying elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_exists_maximal_above__p2m_74778092_2591_4f0d_adff_b80207b549ce_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (x : α) (hx : P x) :
    ∃ y, P y ∧ x ≤ y ∧ ∀ z, P z → y ≤ z → z = y := by sorry
