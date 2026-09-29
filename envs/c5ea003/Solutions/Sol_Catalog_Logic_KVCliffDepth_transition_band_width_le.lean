-- Prove2me | solution 1 for Catalog.Logic.KVCliffDepth.transition_band_width_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:41:48.058986+00:00
-- url     : https://prove2.me/submissions/b6c443bb-587e-4aa9-b160-0083087a438f

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
theorem solution{C A delta p : ℝ} {b b' : ℕ}
    (hC : 0 < C) (hA : 0 < A) (hdelta : 0 < delta) (hp : 3 ≤ p)
    (hb : delta < C * (A / 2 ^ b) ^ p ∧ C * (A / 2 ^ b) ^ p < 5000 * delta)
    (hb' : delta < C * (A / 2 ^ b') ^ p ∧ C * (A / 2 ^ b') ^ p < 5000 * delta) :
    b' ≤ b + 4 := by
  by_contra hcon
  push_neg at hcon
  have hb5 : b + 5 ≤ b' := by omega
  have h2b : (0:ℝ) < 2 ^ b := by positivity
  have h2b' : (0:ℝ) < 2 ^ b' := by positivity
  have hApos : (0:ℝ) < A / 2 ^ b' := by positivity
  have h1 : (2:ℝ) ^ b * 32 ≤ 2 ^ b' := by
    have hmono : (2:ℝ) ^ (b + 5) ≤ 2 ^ b' := pow_le_pow_right₀ (by norm_num) hb5
    calc (2:ℝ) ^ b * 32 = 2 ^ (b + 5) := by rw [pow_add]; norm_num
      _ ≤ 2 ^ b' := hmono
  have hstep : 32 * (A / 2 ^ b') ≤ A / 2 ^ b := by
    rw [mul_div_assoc', div_le_div_iff₀ h2b' h2b]
    nlinarith [hA.le, h1]
  have hposp : (0:ℝ) < (A / 2 ^ b') ^ p := Real.rpow_pos_of_pos hApos p
  have h32 : (32768:ℝ) ≤ (32:ℝ) ^ p := by
    have hmono : (32:ℝ) ^ (3:ℝ) ≤ (32:ℝ) ^ p :=
      (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 32)).mpr hp
    have h3 : (32:ℝ) ^ (3:ℝ) = 32768 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]; norm_num
    linarith [h3 ▸ hmono]
  have hmono : (32 * (A / 2 ^ b')) ^ p ≤ (A / 2 ^ b) ^ p :=
    Real.rpow_le_rpow (by positivity) hstep (by linarith)
  have hsplit : (32 * (A / 2 ^ b')) ^ p = (32:ℝ) ^ p * (A / 2 ^ b') ^ p :=
    Real.mul_rpow (by norm_num) hApos.le
  have hratio : 32768 * (A / 2 ^ b') ^ p ≤ (A / 2 ^ b) ^ p := by
    nlinarith [hsplit ▸ hmono, hposp, h32]
  nlinarith [hb.2, hb'.1, hratio, hC, hdelta]
