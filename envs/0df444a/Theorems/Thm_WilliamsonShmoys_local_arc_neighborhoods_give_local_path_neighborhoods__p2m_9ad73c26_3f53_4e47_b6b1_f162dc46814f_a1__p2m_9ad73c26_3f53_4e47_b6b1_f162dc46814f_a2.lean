-- Prove2me | Theorems.Thm_WilliamsonShmoys_local_arc_neighborhoods_give_local_path_neighborhoods__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a1__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a2
-- name    : WilliamsonShmoys.local_arc_neighborhoods_give_local_path_neighborhoods__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a1__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:43:02.993383+00:00
-- url     : https://prove2.me/theorems/69f3d9b4-1d7b-477d-ae48-060663682a4f
-- title:
--   Local arcs give local path accessibility
-- statement:
--   Given the local arc condition, each open neighborhood U of x contains a smaller open neighborhood V such that every point y in V can be joined to x by a continuous path in U. For y = x use the constant path; otherwise forget injectivity of the supplied local arc. This removes injectivity from the local hypothesis while preserving the neighborhood containment and path range needed by the next step. The point-equals-basepoint case is handled explicitly by the constant path.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.local_arc_neighborhoods_give_local_path_neighborhoods__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a1__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a2 {X : Type} [MetricSpace X] {s : Set X} (hlocal : ∀ x : s, ∀ U : Set s, IsOpen U → x ∈ U → ∃ V : Set s, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y, y ∈ V → y ≠ x → ∃ γ : ℝ → s, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U) : ∀ x : s, ∀ U : Set s, IsOpen U → x ∈ U → ∃ V : Set s, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, ∃ γ : ℝ → s, ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U := by sorry
