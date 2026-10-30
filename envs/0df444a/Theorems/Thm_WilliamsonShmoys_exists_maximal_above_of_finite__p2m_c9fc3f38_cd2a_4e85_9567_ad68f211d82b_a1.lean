-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_above_of_finite__p2m_c9fc3f38_cd2a_4e85_9567_ad68f211d82b_a1
-- name    : WilliamsonShmoys.exists_maximal_above_of_finite__p2m_c9fc3f38_cd2a_4e85_9567_ad68f211d82b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:41:15.800152+00:00
-- url     : https://prove2.me/theorems/c033431d-bd2e-44b0-8ed7-f6932390587c
-- title:
--   A finite partial order has a maximal predicate-satisfying extension
-- statement:
--   In a finite partial order, any element satisfying a predicate lies below a predicate-satisfying element that has no strictly larger predicate-satisfying element.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_above_of_finite__p2m_c9fc3f38_cd2a_4e85_9567_ad68f211d82b_a1 {α : Type} [PartialOrder α] [Finite α] (x : α) (P : α → Prop) (hP : P x) : ∃ y, x ≤ y ∧ P y ∧ ∀ z, y ≤ z → P z → z = y := by sorry
