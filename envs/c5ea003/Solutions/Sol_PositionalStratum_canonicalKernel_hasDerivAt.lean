-- Prove2me | solution 1 for PositionalStratum.canonicalKernel_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:53:40.537537+00:00
-- url     : https://prove2.me/submissions/4434a0a9-4179-45c5-ae30-84d7f03cf600

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
theorem solution{r : ℝ} (hr : 0 < r) :
    HasDerivAt captureCDF (canonicalKernel r) r := by
  have hsq : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hr)
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt r)) r := Real.hasDerivAt_sqrt (ne_of_gt hr)
  have hinv : HasDerivAt (fun x => (Real.sqrt x)⁻¹)
      (-(1 / (2 * Real.sqrt r)) / Real.sqrt r ^ 2) r := hs.inv hsq
  have hsub := (hasDerivAt_const r (1 : ℝ)).sub hinv
  have hsq2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hval : 0 - -(1 / (2 * Real.sqrt r)) / Real.sqrt r ^ 2 = canonicalKernel r := by
    rw [hsq2, canonicalKernel]
    field_simp
    ring
  have : HasDerivAt (fun x => 1 - (Real.sqrt x)⁻¹) (canonicalKernel r) r := by
    rw [← hval]; exact hsub
  have hcast : captureCDF = fun x => 1 - (Real.sqrt x)⁻¹ := by
    funext x; rw [captureCDF, one_div]
  rw [hcast]
  exact this
