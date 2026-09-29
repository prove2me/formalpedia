-- Prove2me | Definitions.Def_NumberTheory_EOSRampZetaBridge
-- name    : NumberTheory_EOSRampZetaBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:07:24.543892+00:00
-- url     : https://prove2.me/theorems/6bbf3ce3-7969-499d-802c-813f28206c30
-- title:
--   Aether Catalog definitions — NumberTheory_EOSRampZetaBridge
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.EOSRampZetaBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/EOSRampZetaBridge.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_EOSWidthMonotoneRamp
/-
# The ramp's failure-mass generating function is an Euler factor of `ζ`

Third file of the NET-27 formalisation, after `EOSWidthMonotoneRamp.lean` and
`EOSExclusiveDimGenericity.lean`.

In the hyperplane model of `EOSWidthRamp`, the failure probability at exclusive width `k` over
the field `𝔽_p` is exactly `p^{-k}`.  Summing the failure mass over all widths therefore produces
the local Euler factor `(1 - p^{-1})^{-1}`; damping the widths by an exponent `s` produces
`(1 - p^{-s})^{-1}`.  Multiplying over all characteristics `p` gives the Riemann zeta function.

* `EOSZeta.rampSeries_eq_eulerFactor` — `∑_k (p^{-s})^k = (1 - p^{-s})^{-1}` for `Re s > 1`;
* `EOSZeta.totalFailureMass_eq_eulerFactor_one` — the real total failure mass of the ramp,
  `∑_k P(fail at width k) = (1 - p^{-1})^{-1}`, i.e. the `s = 1` Euler factor, computed from the
  model rather than postulated;
* `EOSZeta.tprod_rampSeries_eq_riemannZeta` — **the bridge**: the product over all
  characteristics of the damped failure masses of the reliability ramps equals `ζ(s)`
  for `Re s > 1`.

This is a genuine cross-domain statement: the left-hand side is assembled purely from the
finite-field reliability model of `EOSWidthMonotoneRamp.lean`, the right-hand side is the
analytic Riemann zeta function.  It also explains *why* the ramp cannot be a cliff: a cliff
would make the failure mass a finite sum, destroying the Euler factor.
-/


open Filter Topology Complex

namespace EOSZeta

/-- The width-damped failure-mass series of the ramp at characteristic `p` and exponent `s`:
each width `k` contributes its failure probability `p^{-k}`, damped to `p^{-ks}`. -/
noncomputable def rampSeries (p : ℕ) (s : ℂ) : ℂ := ∑' k : ℕ, ((p : ℂ) ^ (-s)) ^ k






end EOSZeta


