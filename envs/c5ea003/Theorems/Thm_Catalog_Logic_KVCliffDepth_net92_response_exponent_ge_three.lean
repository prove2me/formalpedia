-- Prove2me | Theorems.Thm_Catalog_Logic_KVCliffDepth_net92_response_exponent_ge_three
-- name    : Catalog.Logic.KVCliffDepth.net92_response_exponent_ge_three
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:19:33.813243+00:00
-- url     : https://prove2.me/theorems/e7dfac4c-0dbe-4991-ae2d-360778fc2a47
-- title:
--   The NET-92 exponent.
-- statement:
--   **The NET-92 exponent.**  If the excess log-perplexity follows a power law
--   `D(x) = C x ^ p` in the quantisation step `x`, then the two measured arms force `p > 3`:
--   sixteen times the step must multiply the damage by more than `4096`.  (Compare
--   `Algebra.KVCacheResponseExponent.net94_forces_quintic_key_response`, the analogous
--   computation for the NET-94 bracket.)
--
--   ```lean
--   theorem Catalog.Logic.KVCliffDepth.net92_response_exponent_ge_three{C x p : ℝ} (hC : 0 < C) (hx : 0 < x)
--       (h8 : C * x ^ p ≤ 1 / 1000) (h4 : 5 ≤ C * (16 * x) ^ p) : 3 < p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/KVCliffDepthAmplification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/KVCliffDepthAmplification.lean#L164

-- Thm stub generated from Logic/KVCliffDepthAmplification.lean
import Mathlib
import Definitions.Def_Logic_KVCliffDepthAmplification
/-
# NET-92 cycle: depth amplification cannot make a cliff — the homogeneity obstruction

The NET-92 folklore explanation of the `q4_0` collapse is *error amplification through depth*:
"a small key error is multiplied through every softmax boundary of every layer".  This file
takes that explanation seriously enough to formalise it, and then shows that **it cannot be
the whole story**.

Model the propagation of a per-layer quantisation error `ε` through `L` layers with a linear
amplification factor `κ ≥ 1`:

`layerErr κ ε 0 = 0`,  `layerErr κ ε (L+1) = κ * layerErr κ ε L + ε`.

* `layerErr_closed` — the closed form `ε (κ^L − 1)/(κ − 1)` (geometric series, by induction);
* `layerErr_ge_pow` — the error really is exponential in depth, `ε κ^L ≤ layerErr κ ε (L+1)`;
* `layerErr_smul` — **and it is exactly homogeneous of degree one in `ε`**.

Homogeneity is the obstruction.  Going from `q8_0` to `q4_0` multiplies the raw per-tensor
step by `16`, so *any* degree-one (or sub-degree-one) error model multiplies the certified
damage by at most `16`, no matter how large `κ` or `L` are: `net92_refutes_subhomogeneous`.
NET-92 measured a factor `ln(2714.6042/7.1093) / ln(7.1162/7.1093) ≈ 6128` in excess
log-perplexity.  Hence:

> **The depth-amplification story, calibrated at 8 bits, under-predicts the 4-bit collapse by
> more than two orders of magnitude.  The cliff is a threshold phenomenon, not a gain.**

That is the same conclusion the gap-threshold files of the catalog
(`Algebra.KVCacheArgmaxThreshold`) reach from the mechanism side, obtained here from the
response-function side, and it upgrades `Algebra.KVCacheResponseExponent`'s NET-94 exponent
computation to the NET-92 numbers: the measured pair forces a response exponent `≥ 3`
(`net92_response_exponent_ge_three`), and with exponent `p ≥ 3` the whole free-to-annihilated
transition is confined to at most `4` bit widths (`transition_band_width_le`).
-/

open Catalog.Logic.KVCliffDepth

open Real

/-! ## Linear error propagation through depth -/









/-! ## The NET-92 numbers -/






/-! ## What the data do force: a response exponent at least three -/

theorem Catalog.Logic.KVCliffDepth.net92_response_exponent_ge_three{C x p : ℝ} (hC : 0 < C) (hx : 0 < x)
    (h8 : C * x ^ p ≤ 1 / 1000) (h4 : 5 ≤ C * (16 * x) ^ p) : 3 < p := by sorry
