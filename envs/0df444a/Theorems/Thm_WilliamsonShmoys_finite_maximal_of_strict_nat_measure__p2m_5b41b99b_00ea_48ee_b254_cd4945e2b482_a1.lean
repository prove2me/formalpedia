-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_of_strict_nat_measure__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a1
-- name    : WilliamsonShmoys.finite_maximal_of_strict_nat_measure__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:10:57.800219+00:00
-- url     : https://prove2.me/theorems/e87f9b24-47cd-4882-abfb-5483c6eca389
-- title:
--   Finite maximality from a strictly increasing measure
-- statement:
--   In a finite partially ordered type, if a natural-valued measure strictly increases on every proper comparable pair, every nonempty predicate has a maximal element within that predicate. Choose an element maximizing the measure among predicate-satisfying elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_of_strict_nat_measure__p2m_5b41b99b_00ea_48ee_b254_cd4945e2b482_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) (μ : α → ℕ)
    (hstrict : ∀ ⦃a b : α⦄, a ≤ b → a ≠ b → μ a < μ b)
    (hne : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → a ≤ b → b = a := by sorry
