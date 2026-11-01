-- Prove2me | Theorems.Thm_finite_partial_order_has_maximal_above__p2m_b857a82c_8bba_4f53_a10b_55c8fcca96a0_a1
-- name    : finite_partial_order_has_maximal_above__p2m_b857a82c_8bba_4f53_a10b_55c8fcca96a0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:38:06.110798+00:00
-- url     : https://prove2.me/theorems/888f98af-a15f-4d5f-aba8-e2266730370f
-- title:
--   Maximal element above a point in a finite partial order
-- statement:
--   In a finite partial order, every element of a predicate-satisfying subset lies below a maximal element of that subset. This isolates the finite maximality argument from the planar drawing predicate. It can be proved by giving α a Fintype instance and applying the maximal-element result for a nonempty subset of a finite partial order. The parent uses α = SimpleGraph V and P G := K ≤ G ∧ HasPlanarDrawingOn G; its finite-type obligation is discharged by encoding each graph’s edge set as a Boolean-valued function on Sym2 V.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_partial_order_has_maximal_above__p2m_b857a82c_8bba_4f53_a10b_55c8fcca96a0_a1
    {α : Type} [PartialOrder α] [Finite α]
    (P : α → Prop) (a : α) (ha : P a) :
    ∃ b, a ≤ b ∧ P b ∧ ∀ c, b ≤ c → P c → c = b := by sorry
