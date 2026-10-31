-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_poset_has_maximal__p2m_d962869e_258d_4947_a612_83f18b157228_a1
-- name    : WilliamsonShmoys.finite_poset_has_maximal__p2m_d962869e_258d_4947_a612_83f18b157228_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:23:37.270347+00:00
-- url     : https://prove2.me/theorems/e20ce14f-af43-46fb-8d8a-7e149a68636a
-- title:
--   A finite partial order has a maximal element in every nonempty subset
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element with no strictly larger element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_poset_has_maximal__p2m_d962869e_258d_4947_a612_83f18b157228_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (S : α → Prop) (hS : ∃ x, S x) :
    ∃ x, S x ∧ ∀ y, S y → x ≤ y → y ≤ x := by
  sorry
