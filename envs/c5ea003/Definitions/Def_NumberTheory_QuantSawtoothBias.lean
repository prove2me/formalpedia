-- Prove2me | Definitions.Def_NumberTheory_QuantSawtoothBias
-- name    : NumberTheory_QuantSawtoothBias
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:12.581714+00:00
-- url     : https://prove2.me/theorems/4c0c6b60-8773-4f67-a381-42885dc6c8d1
-- title:
--   Aether Catalog definitions — NumberTheory_QuantSawtoothBias
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.QuantSawtoothBias`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/QuantSawtoothBias.lean by skeleton subtraction
import Mathlib
/-
# The exact parity law for round-to-nearest bias on a rational mesh

A round-to-nearest quantizer is usually modelled as adding *zero-mean* noise.  This file shows
that the zero-mean assumption is an arithmetic statement about the **denominator** of the
weights relative to the mesh, and that it fails precisely on the meshes that hardware uses.

Write `sawtooth x = round x - x` for the signed rounding error at unit mesh (Mathlib's `round`
rounds ties upwards).  For a full period of the rational mesh `(1/q)ℤ` we prove

`∑_{j<q} sawtooth (j/q) = ⌊q/2⌋ − (q−1)/2`,

hence

* `sawtooth_period_sum_odd`  : the sum is **exactly 0** when `q` is odd;
* `sawtooth_period_sum_even` : the sum is **exactly 1/2** when `q` is even.

The whole bias is the single tie `j = q/2`, which exists only for even `q`.  Since
`k ↦ k·p mod q` permutes `ZMod q` when `gcd(p,q) = 1`, the same two values are obtained along
*any* arithmetic progression `k·p/q` (`sawtooth_progression_sum`, `sawtooth_progression_odd`,
`sawtooth_progression_even`) — the bias is invariant under the multiplier, a purely
number-theoretic rigidity.

Specialising to `q = 2 ^ b` (`sawtooth_dyadic_bias`): every dyadic — i.e. every real —
quantization grid carries a coherent `+1/2`-step bias per period, which does **not** average
away with width.  This is the arithmetic reason why round-to-nearest damage in the NET-52
measurements is systematic rather than noise-like, and why error *compensation* (rather than a
better choice of scale) is what is needed below the empirical cliff.
-/

namespace Catalog.NumberTheory.QuantSawtooth

open Finset

/-- The signed round-to-nearest error at unit mesh. -/
noncomputable def sawtooth (x : ℝ) : ℝ := (round x : ℝ) - x




/-! ## Rounding on the mesh `(1/q)ℤ` -/








/-! ## Invariance along arithmetic progressions -/







end Catalog.NumberTheory.QuantSawtooth


