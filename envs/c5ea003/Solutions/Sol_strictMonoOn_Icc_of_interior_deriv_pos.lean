-- Prove2me | solution 1 for strictMonoOn_Icc_of_interior_deriv_pos
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T19:03:51.133374+00:00
-- url     : https://prove2.me/submissions/b3d4010e-04aa-42d2-9f0c-debee6044ed9

import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set

theorem solution
    (f f' : ℝ → ℝ) (a b : ℝ)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < f' x) :
    StrictMonoOn f (Set.Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) hcont
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x hx).deriv]
  exact hpos x hx
