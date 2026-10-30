-- Prove2me | Theorems.Thm_WilliamsonShmoys_local_path_accessibility_gives_arcs__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a1
-- name    : WilliamsonShmoys.local_path_accessibility_gives_arcs__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:36:02.327902+00:00
-- url     : https://prove2.me/theorems/b6beab04-6e49-4004-b2f8-5bb88a7da211
-- title:
--   Local path accessibility and path connectedness give arcs
-- statement:
--   In a path-connected metric subspace with local path accessibility at every point and in every open neighborhood, each pair of distinct points can be joined by an injective continuous arc contained in the subspace.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.local_path_accessibility_gives_arcs__p2m_9ad73c26_3f53_4e47_b6b1_f162dc46814f_a1 {X : Type} [MetricSpace X] {s : Set X} (hpath : IsPathConnected s) (hlocalPath : ∀ x : s, ∀ U : Set s, IsOpen U → x ∈ U → ∃ V : Set s, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, ∃ γ : ℝ → s, ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U) (a b : s) (hne : a ≠ b) : ∃ φ : ℝ → X, ContinuousOn φ (Set.Icc 0 1) ∧ Set.InjOn φ (Set.Icc 0 1) ∧ φ 0 = a.val ∧ φ 1 = b.val ∧ ∀ t ∈ Set.Icc 0 1, φ t ∈ s := by sorry
