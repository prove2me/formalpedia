-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_of_bounded_rank__p2m_79adc0d7_3a11_418b_99ea_c41dca74eed5_a3
-- name    : WilliamsonShmoys.exists_maximal_of_bounded_rank__p2m_79adc0d7_3a11_418b_99ea_c41dca74eed5_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:13:50.969648+00:00
-- url     : https://prove2.me/theorems/6e6759d9-0315-429e-bbc6-8889f8511f98
-- title:
--   Maximal element from a bounded natural rank
-- statement:
--   A starting candidate has a maximal valid extension if every valid candidate above it has bounded natural rank and every proper valid extension strictly increases that rank.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_of_bounded_rank__p2m_79adc0d7_3a11_418b_99ea_c41dca74eed5_a3 {α : Type} (le : α → α → Prop) (Q : α → Prop) (r : α → Nat) (a : α) (ha : Q a) (hrefl : le a a) (B : Nat) (hbound : ∀ x : α, le a x → Q x → r x ≤ B) (hstrict : ∀ x y : α, le a x → Q x → le x y → Q y → x ≠ y → r x < r y) : ∃ w : α, le a w ∧ Q w ∧ ∀ x : α, le w x → Q x → x = w := by sorry
