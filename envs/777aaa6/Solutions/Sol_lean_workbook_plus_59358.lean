-- Prove2me | solution 1 for lean_workbook_plus_59358
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:17:41.411287+00:00
-- url     : https://prove2.me/submissions/9e05b7c4-d519-4e6d-bc7b-93c3511f27c2

import Mathlib.Topology.Instances.Real.Lemmas

theorem solution (D : Set ℝ) (f : ℝ → ℝ) (hD : IsCompact D)
    (hf : ContinuousOn f D) : IsCompact (Set.image f D) := by
  exact hD.image_of_continuousOn hf

#print axioms solution
