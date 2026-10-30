-- Prove2me | Theorems.Thm_WilliamsonShmoys_path_segment_image_locally_connected__p2m_a6096ab3_3a99_48ee_9dc7_1633fd090d2c_a1
-- name    : WilliamsonShmoys.path_segment_image_locally_connected__p2m_a6096ab3_3a99_48ee_9dc7_1633fd090d2c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:17:31.014855+00:00
-- url     : https://prove2.me/theorems/430e83e9-913b-40ed-87cc-0e4a575c7435
-- title:
--   Local connectedness of a restricted path image
-- statement:
--   The image subtype of the restricted path is locally connected. Prove the stronger local path-connectedness by factoring the restriction as a continuous surjection from the interval subtype to the image subtype. The interval subtype is convex, hence locally path-connected by `Convex.locallyPathConnectedSpace`. The surjection is a quotient map: the domain is compact, the image subtype is Hausdorff, and the map is closed since images of closed subsets of the compact domain are compact. Apply Mathlib’s `Topology.IsQuotientMap.locallyPathConnectedSpace`; its local-connectedness instance yields this conclusion. This isolates the parent’s core topological argument. The remaining work in the child is establishing the quotient-map facts for this specific restricted map.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.path_segment_image_locally_connected__p2m_a6096ab3_3a99_48ee_9dc7_1633fd090d2c_a1 (γ : ℝ → ℝ × ℝ) (hcont : ContinuousOn γ (Set.Icc 0 1)) : LocallyConnectedSpace (γ '' Set.Icc 0 1) := by sorry
