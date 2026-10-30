-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_injective_subcurve__p2m_bb286dfb_9295_4042_a06e_339ab0b1b6a8_a2
-- name    : WilliamsonShmoys.exists_injective_subcurve__p2m_bb286dfb_9295_4042_a06e_339ab0b1b6a8_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:57:34.096228+00:00
-- url     : https://prove2.me/theorems/2a816385-c89c-4f86-af76-d62ca3e4e97f
-- title:
--   An injective subcurve exists in the image of a planar path
-- statement:
--   For a continuous planar path with distinct endpoints, find an injective continuous curve with the same endpoints and image contained in the original path image. The parent transfers its vertex and edge avoidance to this curve. A proof route is to show the path image is a Peano continuum and apply arcwise connectedness; the child’s arc extraction is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_injective_subcurve__p2m_bb286dfb_9295_4042_a06e_339ab0b1b6a8_a2 (γ : ℝ → ℝ × ℝ) (hcont : ContinuousOn γ (Set.Icc 0 1)) (hne : γ 0 ≠ γ 1) : ∃ γ' : ℝ → ℝ × ℝ, ContinuousOn γ' (Set.Icc 0 1) ∧ Set.InjOn γ' (Set.Icc 0 1) ∧ γ' 0 = γ 0 ∧ γ' 1 = γ 1 ∧ (∀ t ∈ Set.Icc 0 1, ∃ s ∈ Set.Icc 0 1, γ s = γ' t) := by sorry
