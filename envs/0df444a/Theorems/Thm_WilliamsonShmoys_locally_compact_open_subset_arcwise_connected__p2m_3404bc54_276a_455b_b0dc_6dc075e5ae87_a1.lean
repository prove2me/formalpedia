-- Prove2me | Theorems.Thm_WilliamsonShmoys_locally_compact_open_subset_arcwise_connected__p2m_3404bc54_276a_455b_b0dc_6dc075e5ae87_a1
-- name    : WilliamsonShmoys.locally_compact_open_subset_arcwise_connected__p2m_3404bc54_276a_455b_b0dc_6dc075e5ae87_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:43:12.305716+00:00
-- url     : https://prove2.me/theorems/169c9a8e-df8f-41e3-a03b-f96007c76cfa
-- title:
--   Connected open subsets of locally compact locally connected metric spaces are arcwise connected
-- statement:
--   In a locally compact, locally connected metric space, every connected open subset contains an injective continuous arc between any two distinct points.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.locally_compact_open_subset_arcwise_connected__p2m_3404bc54_276a_455b_b0dc_6dc075e5ae87_a1 {X : Type} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] {U : Set X} (hUopen : IsOpen U) (hUconnected : IsConnected U) (x : X) (hxU : x ∈ U) : ∀ y : X, y ∈ U → y ≠ x → ∃ γ : ℝ → X, ContinuousOn γ (Set.Icc 0 1) ∧ Set.InjOn γ (Set.Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ U := by sorry
