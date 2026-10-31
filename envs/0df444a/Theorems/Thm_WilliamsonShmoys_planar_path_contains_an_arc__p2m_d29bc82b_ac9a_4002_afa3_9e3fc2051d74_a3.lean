-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_path_contains_an_arc__p2m_d29bc82b_ac9a_4002_afa3_9e3fc2051d74_a3
-- name    : WilliamsonShmoys.planar_path_contains_an_arc__p2m_d29bc82b_ac9a_4002_afa3_9e3fc2051d74_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:27:22.601492+00:00
-- url     : https://prove2.me/theorems/e434a331-6955-4613-9b53-3e7bcea3fae5
-- title:
--   An arc inside a planar path image
-- statement:
--   Every continuous path in the plane with distinct endpoints contains the image of an injectively parametrized continuous arc joining those endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_path_contains_an_arc__p2m_d29bc82b_ac9a_4002_afa3_9e3fc2051d74_a3
    (gamma : ℝ → ℝ × ℝ)
    (hcont : ContinuousOn gamma (Set.Icc 0 1))
    (hone : gamma 1 ≠ gamma 0) :
    ∃ delta : ℝ → ℝ × ℝ,
      ContinuousOn delta (Set.Icc 0 1) ∧
      Set.InjOn delta (Set.Icc 0 1) ∧
      delta 0 = gamma 0 ∧ delta 1 = gamma 1 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ s ∈ Set.Icc (0 : ℝ) 1, delta t = gamma s) := by sorry
