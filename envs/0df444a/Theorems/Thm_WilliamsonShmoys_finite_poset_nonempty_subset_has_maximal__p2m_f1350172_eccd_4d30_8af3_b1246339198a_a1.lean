-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_poset_nonempty_subset_has_maximal__p2m_f1350172_eccd_4d30_8af3_b1246339198a_a1
-- name    : WilliamsonShmoys.finite_poset_nonempty_subset_has_maximal__p2m_f1350172_eccd_4d30_8af3_b1246339198a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:35:32.556258+00:00
-- url     : https://prove2.me/theorems/e1d45188-9424-4069-9c81-8ace15e2790e
-- title:
--   A nonempty subset of a finite partial order has a maximal element
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element with no strictly greater element in that subset. The statement includes finite types with a single element and does not require the subset to be closed under the order.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_poset_nonempty_subset_has_maximal__p2m_f1350172_eccd_4d30_8af3_b1246339198a_a1
    {α : Type} [Finite α] [PartialOrder α]
    (Q : α → Prop) (hQ : ∃ a, Q a) :
    ∃ a, Q a ∧ ∀ b, a ≤ b → Q b → b ≤ a := by
  sorry
