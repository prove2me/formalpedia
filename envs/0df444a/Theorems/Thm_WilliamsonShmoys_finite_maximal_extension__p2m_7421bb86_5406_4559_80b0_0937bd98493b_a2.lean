-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
-- name    : WilliamsonShmoys.finite_maximal_extension__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:43:32.76035+00:00
-- url     : https://prove2.me/theorems/d329ab81-8444-4da6-ab0c-295d72e05766
-- title:
--   Maximal extension in a finite partial order
-- statement:
--   For any finite partially ordered type and any inhabited property class, every member lies below a maximal member of that class. This separates the finite-order argument from planarity; the proof route is finite induction or a maximal-chain argument. The witness assumption hx handles the boundary case where the class might otherwise be empty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension__p2m_7421bb86_5406_4559_80b0_0937bd98493b_a2 {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (x : α) (hx : P x) : ∃ y, x ≤ y ∧ P y ∧ ∀ z, y ≤ z → P z → z ≤ y := by sorry
