-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_element_above_of_finite_partialOrder__p2m_af13f63f_cd05_40af_9e3b_bd5fcae2a11f_a1
-- name    : WilliamsonShmoys.exists_maximal_element_above_of_finite_partialOrder__p2m_af13f63f_cd05_40af_9e3b_bd5fcae2a11f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:09:55.81965+00:00
-- url     : https://prove2.me/theorems/a87b3205-70d0-4852-a75f-43f6f3e7f22a
-- title:
--   A finite partial order has a maximal element above any eligible element
-- statement:
--   In a finite partially ordered type, any element satisfying a predicate lies below a predicate-satisfying element that has no strictly larger predicate-satisfying element. Prove by maximizing within the finite set of predicate-satisfying elements above the given element; the empty and singleton cases are included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_element_above_of_finite_partialOrder__p2m_af13f63f_cd05_40af_9e3b_bd5fcae2a11f_a1 {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (a : α) (ha : P a) : ∃ m : α, a ≤ m ∧ P m ∧ ∀ n : α, m ≤ n → P n → n = m := by sorry
