-- Prove2me | Theorems.Thm_WilliamsonShmoys_path_segment_image_compact_path_connected__p2m_a6096ab3_3a99_48ee_9dc7_1633fd090d2c_a1
-- name    : WilliamsonShmoys.path_segment_image_compact_path_connected__p2m_a6096ab3_3a99_48ee_9dc7_1633fd090d2c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:17:26.644436+00:00
-- url     : https://prove2.me/theorems/6c97199d-a93b-4dfe-b927-048d75711cdc
-- title:
--   Compactness and path connectedness of a restricted path image
-- statement:
--   For a map continuous on the closed unit interval, its image is compact and path-connected. Compactness follows from compactness of the interval and `IsCompact.image_of_continuousOn`. For path connectedness, use convexity and nonemptiness of the interval with `Convex.isPathConnected`, then map path connectedness through the restricted continuous map. This removes the two routine image properties from the parent while retaining the exact continuity domain and both interval endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.path_segment_image_compact_path_connected__p2m_a6096ab3_3a99_48ee_9dc7_1633fd090d2c_a1 (γ : ℝ → ℝ × ℝ) (hcont : ContinuousOn γ (Set.Icc 0 1)) : IsCompact (γ '' Set.Icc 0 1) ∧ IsPathConnected (γ '' Set.Icc 0 1) := by sorry
