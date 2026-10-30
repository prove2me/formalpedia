-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximizer_of_bounded__p2m_6dfe235c_2d93_4cd3_a1e8_c2011cbaaa57_a1
-- name    : WilliamsonShmoys.exists_maximizer_of_bounded__p2m_6dfe235c_2d93_4cd3_a1e8_c2011cbaaa57_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:17:16.132889+00:00
-- url     : https://prove2.me/theorems/488503b6-6b1c-46bf-9519-ed16f040a7b2
-- title:
--   A bounded natural-valued objective attains a feasible maximum
-- statement:
--   For any nonempty feasible class and a natural-valued objective bounded above by B on that class, some feasible element attains a maximum objective value.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximizer_of_bounded__p2m_6dfe235c_2d93_4cd3_a1e8_c2011cbaaa57_a1 {α : Type} (P : α → Prop) (f : α → Nat) (hP : ∃ x, P x) (B : Nat) (hB : ∀ x, P x → f x ≤ B) : ∃ x, P x ∧ ∀ y, P y → f y ≤ f x := by sorry
