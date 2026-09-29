-- Prove2me | Definitions.Def_Applications_PositionalStratumKernel
-- name    : Applications_PositionalStratumKernel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:26.403912+00:00
-- url     : https://prove2.me/theorems/c36fdcd7-7faf-4918-b852-fb3ef7fafe39
-- title:
--   Aether Catalog definitions — Applications_PositionalStratumKernel
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PositionalStratumKernel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PositionalStratumKernel.lean by skeleton subtraction
import Mathlib
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

namespace PositionalStratum

open Real MeasureTheory intervalIntegral

noncomputable section

/-- The canonical reporting kernel `b(r) = ½ r^{-3/2}`. -/
def canonicalKernel (r : ℝ) : ℝ := 1 / (2 * r * Real.sqrt r)

/-- The capture CDF `x(r) = 1 - r^{-1/2}` (= the balance coordinate measured from the
top of the scale). -/
def captureCDF (r : ℝ) : ℝ := 1 - 1 / Real.sqrt r






/-- The capture probability of the retained window `[1,R]` inside the population
`[1, R_max]`, under the canonical reporting prior. -/
def captureProb (Rmax R : ℝ) : ℝ :=
  (∫ r in (1 : ℝ)..R, canonicalKernel r) / ∫ r in (1 : ℝ)..Rmax, canonicalKernel r





end

end PositionalStratum


