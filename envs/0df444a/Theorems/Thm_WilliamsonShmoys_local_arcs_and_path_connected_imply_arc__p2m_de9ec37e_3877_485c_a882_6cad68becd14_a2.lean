-- Prove2me | Theorems.Thm_WilliamsonShmoys_local_arcs_and_path_connected_imply_arc__p2m_de9ec37e_3877_485c_a882_6cad68becd14_a2
-- name    : WilliamsonShmoys.local_arcs_and_path_connected_imply_arc__p2m_de9ec37e_3877_485c_a882_6cad68becd14_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:27:29.172803+00:00
-- url     : https://prove2.me/theorems/9ad73c26-3f53-4e47-b6b1-f162dc46814f
-- title:
--   Local arc neighborhoods and path connectedness imply arc connectedness
-- statement:
--   In a path-connected metric subspace with the stated local arc-neighborhood property, every pair of distinct points is joined by a continuous injective arc contained in the subspace.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.local_arcs_and_path_connected_imply_arc__p2m_de9ec37e_3877_485c_a882_6cad68becd14_a2 {X : Type} [MetricSpace X] {s : Set X} (hpath : IsPathConnected s) (hlocal : ∀ x : s, ∀ U : Set s, IsOpen U → x ∈ U → ∃ V : Set s, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, y ≠ x → ∃ γ : ℝ → s, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U) (a b : s) (hne : a ≠ b) : ∃ φ : ℝ → X, ContinuousOn φ (Set.Icc 0 1) ∧ Set.InjOn φ (Set.Icc 0 1) ∧ φ 0 = a.val ∧ φ 1 = b.val ∧ ∀ t ∈ Set.Icc 0 1, φ t ∈ s := by sorry
