-- Prove2me | solution 1 for PositionalStratum.capture_curve_not_linear_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:56:39.684583+00:00
-- url     : https://prove2.me/submissions/515491d2-717f-40ba-91e7-71ad1d8b27c1

-- Sol generated from Applications/PositionalStratumKernel.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumKernel
import Theorems.Thm_PositionalStratum_canonicalKernel_continuousOn
import Theorems.Thm_PositionalStratum_canonicalKernel_hasDerivAt
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



lemma captureCDF_one : captureCDF 1 = 0 := by
  simp [captureCDF]



/-- **The canonical kernel integrates to the capture CDF**: `∫_1^R ½ r^{-3/2} = 1 - R^{-1/2}`. -/
theorem canonical_integral {R : ℝ} (hR : 1 ≤ R) :
    ∫ r in (1 : ℝ)..R, canonicalKernel r = captureCDF R := by
  have hderiv : ∀ r ∈ Set.uIcc (1 : ℝ) R, HasDerivAt captureCDF (canonicalKernel r) r := by
    intro r hr
    have hsub : Set.uIcc (1 : ℝ) R ⊆ Set.Ici (1 : ℝ) := by
      rw [Set.uIcc_of_le hR]; exact Set.Icc_subset_Ici_self
    have hr1 : (1 : ℝ) ≤ r := hsub hr
    exact canonicalKernel_hasDerivAt (by linarith)
  have hint : IntervalIntegrable canonicalKernel volume 1 R :=
    (canonicalKernel_continuousOn hR).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, captureCDF_one, sub_zero]




/-- **The capture curve is exactly linear in the balance coordinate.**  Writing
`μ = 1 - R^{-1/2}` for the retained balance mass, `P(μ) = μ / (1 - R_max^{-1/2})`. -/
theorem captureProb_linear {Rmax R : ℝ} (hR : 1 ≤ R) (hmax : 1 < Rmax) :
    captureProb Rmax R = (1 / captureCDF Rmax) * captureCDF R := by
  rw [captureProb, canonical_integral hR, canonical_integral hmax.le]
  field_simp





open PositionalStratum in
theorem solution:
    (∫ _r in (1 : ℝ)..2, (1 : ℝ) / 3) / (∫ _r in (1 : ℝ)..4, (1 : ℝ) / 3)
      ≠ captureProb 4 2 := by
  have h1 : (∫ _r in (1 : ℝ)..2, (1 : ℝ) / 3) = 1 / 3 := by
    rw [intervalIntegral.integral_const]
    norm_num
  have h2 : (∫ _r in (1 : ℝ)..4, (1 : ℝ) / 3) = 1 := by
    rw [intervalIntegral.integral_const]
    norm_num
  have hcap : captureProb 4 2 = 2 - Real.sqrt 2 := by
    rw [captureProb_linear (by norm_num) (by norm_num), captureCDF, captureCDF]
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hs2 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [h4]
    field_simp
    nlinarith [hsq, hs2]
  rw [h1, h2, hcap]
  have hlt : Real.sqrt 2 < 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  intro hcon
  nlinarith [hcon, hlt]
