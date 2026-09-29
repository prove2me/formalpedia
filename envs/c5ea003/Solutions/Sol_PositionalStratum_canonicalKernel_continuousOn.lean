-- Prove2me | solution 1 for PositionalStratum.canonicalKernel_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:53:40.058235+00:00
-- url     : https://prove2.me/submissions/fad3f6a7-623e-4d02-b795-0c5972909374

-- Sol generated from Applications/PositionalStratumKernel.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumKernel
/-
# F2 : the canonical positional prior `b ∝ r^{-3/2}` and the capture curve

The scale × balance formulation says that *balance is position*: the balance coordinate is
`s = r^{-1/2}`, and the reporting prior that is uniform in the balance coordinate is the
canonical kernel

  `b(r) = 1 / (2 · r · √r)  =  ½ · r^{-3/2}`,

whose primitive is the capture CDF `x(r) = 1 - r^{-1/2}`.

What is proved.

* `canonicalKernel_hasDerivAt`, `canonical_integral` — the kernel integrates to the capture
  CDF: `∫_1^R b = 1 - R^{-1/2}`.  Equivalently (`canonical_is_uniform_in_balance`) the mass
  the canonical prior gives to `[1,R]` equals the *length of the balance interval*
  `[R^{-1/2}, 1]`: the canonical prior is exactly the uniform prior in the balance
  coordinate.
* `captureProb_linear` — the capture curve is **exactly linear** in `μ = 1 - R^{-1/2}` with
  slope `1/(1 - R_max^{-1/2})`, i.e. `P(μ) = μ / (1 - R_max^{-1/2})`.
* `kernel_unique_of_capture_law` — the converse: *linear iff canonical*.  A continuous
  reporting density whose capture curve is proportional to `1 - R^{-1/2}` must be a
  multiple of the canonical kernel.  So the canonical prior is not a convention but the
  unique shape compatible with a linear capture curve.
* `capture_curve_not_linear_of_uniform` — a concrete non-canonical prior (the uniform
  density on `[1, R_max]`) has a capture curve that is *not* proportional to the canonical
  one, confirming the "only if" direction has content.
-/

open PositionalStratum

open Real MeasureTheory intervalIntegral

noncomputable section















open PositionalStratum in
theorem solution{R : ℝ} (hR : 1 ≤ R) :
    ContinuousOn canonicalKernel (Set.uIcc (1 : ℝ) R) := by
  have hsub : Set.uIcc (1 : ℝ) R ⊆ Set.Ici (1 : ℝ) := by
    rw [Set.uIcc_of_le hR]
    exact Set.Icc_subset_Ici_self
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := hsub hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hden : 2 * x * Real.sqrt x ≠ 0 := by
    have : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
    positivity
  refine ContinuousAt.continuousWithinAt ?_
  have hcont : ContinuousAt (fun y : ℝ => 2 * y * Real.sqrt y) x := by
    exact (continuousAt_const.mul continuousAt_id).mul (Real.continuous_sqrt.continuousAt)
  exact continuousAt_const.div hcont hden
