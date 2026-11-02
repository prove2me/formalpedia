-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_finset_maximal__p2m_d87be54e_bfcb_4aba_9277_804ad42ab6ab_a1
-- name    : WilliamsonShmoys.finite_finset_maximal__p2m_d87be54e_bfcb_4aba_9277_804ad42ab6ab_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:22:33.763881+00:00
-- url     : https://prove2.me/theorems/5b519eef-da06-4aff-83ba-7a835c0862d2
-- title:
--   Maximal element of a nonempty finite subset of a partial order
-- statement:
--   Every nonempty finite subset of a partial order contains an element with no strictly larger element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_finset_maximal__p2m_d87be54e_bfcb_4aba_9277_804ad42ab6ab_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (s : Finset α) (hs : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, a ≤ b → b ≤ a := by sorry
