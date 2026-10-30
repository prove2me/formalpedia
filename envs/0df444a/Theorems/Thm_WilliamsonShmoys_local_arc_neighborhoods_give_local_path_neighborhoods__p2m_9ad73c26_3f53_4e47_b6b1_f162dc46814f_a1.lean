-- Prove2me | Theorems.Thm_WilliamsonShmoys_local_arc_neighborhoods_give_local_path_neighborhoods__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a1
-- name    : WilliamsonShmoys.local_arc_neighborhoods_give_local_path_neighborhoods__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:03.435263+00:00
-- url     : https://prove2.me/theorems/ea4c5e6b-79e3-4c5b-8f05-42b60aa76f9f
-- title:
--   Local arcs give local path accessibility
-- statement:
--   For each open neighborhood U of x in s, the given local arc condition yields an open neighborhood V of x such that every y in V can be joined to x by a continuous path contained in U.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.local_arc_neighborhoods_give_local_path_neighborhoods__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a1 {X : Type} [MetricSpace X] {s : Set X} (hlocal : ∀ x : s, ∀ U : Set s, IsOpen U → x ∈ U → ∃ V : Set s, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, y ≠ x → ∃ γ : ℝ → s, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U) : ∀ x : s, ∀ U : Set s, IsOpen U → x ∈ U → ∃ V : Set s, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, ∃ γ : ℝ → s, ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U := by sorry
