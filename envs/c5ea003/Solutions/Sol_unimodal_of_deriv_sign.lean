-- Prove2me | solution 1 for unimodal_of_deriv_sign
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T18:25:43.633209+00:00
-- url     : https://prove2.me/submissions/68606f30-62a7-4f88-b503-7724a0602b06

import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set

/-- **Siegel 2001, Thm 2.1, p.5 — unimodality from a single-sign-change derivative.** -/
theorem solution
    (φ φ' : ℝ → ℝ) (μ a : ℝ)
    (hd : ∀ x, HasDerivAt φ (φ' x) x)
    (hpos : ∀ x ∈ Ioo (0:ℝ) a, 0 < φ' x)
    (hneg : ∀ x ∈ Ioo a μ, φ' x < 0) :
    StrictMonoOn φ (Icc 0 a) ∧ StrictAntiOn φ (Icc a μ) := by
  constructor
  · apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc 0 a)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
    intro x hx
    exact hpos x (by simpa [interior_Icc] using hx)
  · apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc a μ)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
    intro x hx
    exact hneg x (by simpa [interior_Icc] using hx)
