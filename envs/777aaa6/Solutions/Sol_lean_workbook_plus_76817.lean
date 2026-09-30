-- Prove2me | solution 1 for lean_workbook_plus_76817
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:17:48.45948+00:00
-- url     : https://prove2.me/submissions/e47a60fa-5189-422f-8d29-e574b1cdbd76

import Mathlib.Topology.Instances.Real.Lemmas

theorem solution (f g : ℝ → ℝ) (hf : UniformContinuous f)
    (hg : UniformContinuous g) : UniformContinuous (f ∘ g) := by
  exact hf.comp hg

#print axioms solution
