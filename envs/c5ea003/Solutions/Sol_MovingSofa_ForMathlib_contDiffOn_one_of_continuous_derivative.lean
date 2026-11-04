-- Prove2me | solution 1 for MovingSofa.ForMathlib.contDiffOn_one_of_continuous_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-11-04T02:54:58.31133+00:00
-- url     : https://prove2.me/submissions/3b76321c-abe8-4e39-b73c-237ab444bc80

import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

open Set

theorem solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (f : ℝ → E) (d : s → E) (hd : Continuous d)
    (hf : ∀ t : s, HasDerivWithinAt f (d t) s t) : ContDiffOn ℝ 1 f s := by
  apply (contDiffOn_one_iff_derivWithin hs).mpr
  refine ⟨fun t ht ↦ (hf ⟨t, ht⟩).differentiableWithinAt, ?_⟩
  apply continuousOn_iff_continuous_restrict.mpr
  apply hd.congr
  intro t
  exact ((hf t).derivWithin (hs t t.property)).symm
