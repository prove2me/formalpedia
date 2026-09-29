-- Prove2me | Definitions.Def_Logic_KVCliffDepthAmplification
-- name    : Logic_KVCliffDepthAmplification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:55:28.793363+00:00
-- url     : https://prove2.me/theorems/cdc0960e-95f3-4bd3-a367-907efabaf4eb
-- title:
--   Aether Catalog definitions — Logic_KVCliffDepthAmplification
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.KVCliffDepthAmplification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/KVCliffDepthAmplification.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Logic.KVCliffDepth

open Real

/-! ## Linear error propagation through depth -/

/-- Worst-case logit error after `L` layers, when each layer amplifies the incoming error by
`κ` and injects a fresh quantisation error `ε`. -/
noncomputable def layerErr (kappa eps : ℝ) : ℕ → ℝ
  | 0 => 0
  | L + 1 => kappa * layerErr kappa eps L + eps








/-! ## The NET-92 numbers -/






/-! ## What the data do force: a response exponent at least three -/



end Catalog.Logic.KVCliffDepth


