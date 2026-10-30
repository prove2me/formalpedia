-- Prove2me | Theorems.Thm_locallyConnectedSpace_image_Icc_of_continuousOn__p2m_430e83e9_913b_40ed_87cc_0e4a575c7435_a1
-- name    : locallyConnectedSpace_image_Icc_of_continuousOn__p2m_430e83e9_913b_40ed_87cc_0e4a575c7435_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:24:05.632983+00:00
-- url     : https://prove2.me/theorems/f60b6fbd-a1d3-41a3-a77b-c87ca3cb573b
-- title:
--   Locally connectedness of continuous interval images
-- statement:
--   For a Hausdorff second-countable topological space, the image of the closed unit interval under a continuous-on-the-interval map is locally connected. The image is compact and connected; as a compact Hausdorff second-countable space it is metrizable, so the necessity direction of Hahn–Mazurkiewicz applies. The remaining core obligation is to formalize this classical argument or locate a compatible Mathlib result.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem locallyConnectedSpace_image_Icc_of_continuousOn__p2m_430e83e9_913b_40ed_87cc_0e4a575c7435_a1 {X : Type*} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] (f : ℝ → X) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) : LocallyConnectedSpace (f '' Set.Icc (0 : ℝ) 1) := by sorry
