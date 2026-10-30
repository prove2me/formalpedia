-- Prove2me | Theorems.Thm_WilliamsonShmoys_path_segment_image_peano_properties__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a2
-- name    : WilliamsonShmoys.path_segment_image_peano_properties__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:07:31.573676+00:00
-- url     : https://prove2.me/theorems/a6096ab3-3a99-48ee-9dc7-1633fd090d2c
-- title:
--   Restricted path images are Peano continua
-- statement:
--   The image of the restricted path on `[0,1]` is compact, path-connected, and locally connected as a subspace of the plane.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.path_segment_image_peano_properties__p2m_2a816385_c89c_4f86_af76_d62ca3e4e97f_a2 (γ : ℝ → ℝ × ℝ) (hcont : ContinuousOn γ (Set.Icc 0 1)) : IsCompact (γ '' Set.Icc 0 1) ∧ IsPathConnected (γ '' Set.Icc 0 1) ∧ LocallyConnectedSpace (γ '' Set.Icc 0 1) := by sorry
