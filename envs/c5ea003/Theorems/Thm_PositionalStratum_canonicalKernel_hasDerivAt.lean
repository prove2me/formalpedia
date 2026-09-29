-- Prove2me | Theorems.Thm_PositionalStratum_canonicalKernel_hasDerivAt
-- name    : PositionalStratum.canonicalKernel_hasDerivAt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:59:37.399573+00:00
-- url     : https://prove2.me/theorems/6e7009c6-2a20-47be-8f21-b282d1397a60
-- title:
--   The capture CDF is a primitive of the canonical kernel.
-- statement:
--   The capture CDF is a primitive of the canonical kernel.
--
--   ```lean
--   theorem PositionalStratum.canonicalKernel_hasDerivAt{r : ℝ} (hr : 0 < r) :
--       HasDerivAt captureCDF (canonicalKernel r) r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PositionalStratumKernel.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PositionalStratumKernel.lean#L46

-- Thm stub generated from Applications/PositionalStratumKernel.lean
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

theorem PositionalStratum.canonicalKernel_hasDerivAt{r : ℝ} (hr : 0 < r) :
    HasDerivAt captureCDF (canonicalKernel r) r := by sorry
