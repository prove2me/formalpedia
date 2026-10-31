-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_injective_subpath_in_euclidean_plane__p2m_c87c3c00_b1b8_447c_b699_4692a3a46853_a3
-- name    : WilliamsonShmoys.exists_injective_subpath_in_euclidean_plane__p2m_c87c3c00_b1b8_447c_b699_4692a3a46853_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:08:45.844061+00:00
-- url     : https://prove2.me/theorems/d29bc82b-ac9a-4002-afa3-9e3fc2051d74
-- title:
--   Extract an injective path from a plane path
-- statement:
--   A continuous path on the unit interval in the plane, starting at the origin and ending at a distinct point, contains a continuously parameterized injective path with the same endpoints. Every interior point of the extracted path is attained by the original path at an interior parameter.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_injective_subpath_in_euclidean_plane__p2m_c87c3c00_b1b8_447c_b699_4692a3a46853_a3
    (gamma : ℝ → ℝ × ℝ)
    (hcont : ContinuousOn gamma (Set.Icc 0 1))
    (hzero : gamma 0 = (0 : ℝ × ℝ))
    (hone : gamma 1 ≠ gamma 0) :
    ∃ delta : ℝ → ℝ × ℝ,
      ContinuousOn delta (Set.Icc 0 1) ∧
      Set.InjOn delta (Set.Icc 0 1) ∧
      delta 0 = gamma 0 ∧ delta 1 = gamma 1 ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃ s ∈ Set.Ioo (0 : ℝ) 1, delta t = gamma s) := by sorry
