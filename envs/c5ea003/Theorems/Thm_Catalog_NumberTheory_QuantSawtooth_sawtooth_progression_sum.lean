-- Prove2me | Theorems.Thm_Catalog_NumberTheory_QuantSawtooth_sawtooth_progression_sum
-- name    : Catalog.NumberTheory.QuantSawtooth.sawtooth_progression_sum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:24:56.147076+00:00
-- url     : https://prove2.me/theorems/2921cbe7-5fed-4ebe-a78c-17de7a9d5644
-- title:
--   The period bias is invariant under the multiplier.
-- statement:
--   **The period bias is invariant under the multiplier.**  For `gcd(p,q) = 1` the arithmetic
--   progression `k·p/q`, `k < q`, has exactly the same total rounding error as the standard mesh.
--
--   ```lean
--   theorem Catalog.NumberTheory.QuantSawtooth.sawtooth_progression_sum{p q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime p q) :
--       ∑ k ∈ Finset.range q, sawtooth ((k * p : ℕ) / (q : ℝ))
--         = ((q / 2 : ℕ) : ℝ) - ((q : ℝ) - 1) / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/QuantSawtoothBias.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/QuantSawtoothBias.lean#L187

-- Thm stub generated from NumberTheory/QuantSawtoothBias.lean
import Mathlib
import Definitions.Def_NumberTheory_QuantSawtoothBias
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

open Catalog.NumberTheory.QuantSawtooth

open Finset





/-! ## Rounding on the mesh `(1/q)ℤ` -/








/-! ## Invariance along arithmetic progressions -/

theorem Catalog.NumberTheory.QuantSawtooth.sawtooth_progression_sum{p q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime p q) :
    ∑ k ∈ Finset.range q, sawtooth ((k * p : ℕ) / (q : ℝ))
      = ((q / 2 : ℕ) : ℝ) - ((q : ℝ) - 1) / 2 := by sorry
