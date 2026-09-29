-- Prove2me | solution 1 for Catalog.Logic.KVCliffDepth.net92_response_exponent_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:41:47.343903+00:00
-- url     : https://prove2.me/submissions/910968f0-0f15-4fb0-96cb-86e9fdef338e

-- Sol generated from Logic/KVCliffDepthAmplification.lean
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




open Catalog.Logic.KVCliffDepth in
theorem solution{C x p : ℝ} (hC : 0 < C) (hx : 0 < x)
    (h8 : C * x ^ p ≤ 1 / 1000) (h4 : 5 ≤ C * (16 * x) ^ p) : 3 < p := by
  have hmul : (16 * x) ^ p = 16 ^ p * x ^ p := Real.mul_rpow (by norm_num) hx.le
  have hxp : (0:ℝ) < x ^ p := Real.rpow_pos_of_pos hx p
  have hCx : (0:ℝ) < C * x ^ p := mul_pos hC hxp
  have hbig : 4096 * (C * x ^ p) < 16 ^ p * (C * x ^ p) := by
    have h1 : 5 ≤ 16 ^ p * (C * x ^ p) := by
      calc (5:ℝ) ≤ C * (16 * x) ^ p := h4
        _ = 16 ^ p * (C * x ^ p) := by rw [hmul]; ring
    have h2 : 4096 * (C * x ^ p) ≤ 4096 * (1 / 1000) := by
      exact mul_le_mul_of_nonneg_left h8 (by norm_num)
    have : (4096 : ℝ) * (1 / 1000) < 5 := by norm_num
    linarith
  have hpow : (4096 : ℝ) < 16 ^ p := lt_of_mul_lt_mul_right (by linarith) hCx.le
  have h16 : (4096 : ℝ) = (16 : ℝ) ^ (3 : ℝ) := by
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [h16] at hpow
  exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 16)).mp hpow
