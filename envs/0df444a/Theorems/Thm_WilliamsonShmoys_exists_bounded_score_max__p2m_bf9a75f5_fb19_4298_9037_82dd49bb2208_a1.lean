-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_bounded_score_max__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1
-- name    : WilliamsonShmoys.exists_bounded_score_max__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:09:53.048442+00:00
-- url     : https://prove2.me/theorems/6fdc40f3-39be-4bda-8284-0bd49d008a1f
-- title:
--   Maximum of a bounded natural score on a nonempty predicate
-- statement:
--   If a predicate has at least one witness and its natural-valued score is bounded above, some witness has maximum score. This removes the finite maximization step from the parent. A proof forms the finite set of attainable scores in 0 through B, takes its maximum, and selects a witness attaining it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_bounded_score_max__p2m_bf9a75f5_fb19_4298_9037_82dd49bb2208_a1 {α : Type} (s : α → Prop) (score : α → Nat) (B : Nat) (hbound : ∀ a, s a → score a ≤ B) (hne : ∃ a, s a) : ∃ a, s a ∧ ∀ b, s b → score b ≤ score a := by sorry
