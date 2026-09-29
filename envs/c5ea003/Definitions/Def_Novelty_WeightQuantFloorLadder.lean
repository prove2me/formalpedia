-- Prove2me | Definitions.Def_Novelty_WeightQuantFloorLadder
-- name    : Novelty_WeightQuantFloorLadder
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:07:49.80757+00:00
-- url     : https://prove2.me/theorems/6a7ac2a1-03fd-49e8-b7b4-0b29150bdc63
-- title:
--   Aether Catalog definitions — Novelty_WeightQuantFloorLadder
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.WeightQuantFloorLadder`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/WeightQuantFloorLadder.lean by skeleton subtraction
import Mathlib

/-!
# The weight-quantisation ladder: a geometric law with no bit-width floor (NET-95)

This file formalises the *quantitative* content of the NET-95 measurement
**THE-WEIGHT-FLOOR-COLLAPSED**.  A 7B model was evaluated with `llama-perplexity`
(ctx = 2048, 8 threads, a 250 KB held-out wikitext slice) at seven weight
precisions:

| rung   | bpw  | PPL    |
|--------|------|--------|
| fp16   | 16   | 6.9825 |
| q8_0   | 8.5  | 6.9781 |
| q6_k   | 6.6  | 7.0006 |
| q5_k_m | 5.5  | 7.0427 |
| q4_k_m | 4.8  | 7.1093 |
| q3_k_m | 3.9  | 7.2758 |
| q2_k   | 2.6  | 8.1105 |

The narrative claim attached to this table is that the "sub-6-bit floor" reported
for a toy round-to-nearest quantiser (NET-52) is *not* a law about bit widths:
at scale, with calibration-aware k-quants, the excess perplexity
`E(b) = PPL(b) - PPL(fp16)` is a smooth, convex, purely geometric function of the
bit width, with **no cliff anywhere** between 6.6 and 2.6 bpw.

Everything below is proved from the measured numbers as exact rationals.

## Main results

* `weight_ladder_geometric_band` — the *one-parameter law*.  For **every** pair of
  rungs of the k-quant ladder (not merely adjacent ones), the excess perplexity
  ratio per bit removed lies in the band `[5/2, 3]`:
  `(5/2)^k · E(r)^10 ≤ E(s)^10 ≤ 3^k · E(r)^10`, where `k` is the bit-width gap in
  tenths of a bit.  Ten inequalities, all tight enough that neither endpoint of
  the band can be moved much (the extreme observed per-bit rates are `2.539` and
  `2.982`).
* `weight_ladder_cliff_free` — no pair of rungs exhibits a per-bit degradation
  factor of `4` or more: the ladder is cliff-free in the strong, all-pairs sense.
* `weight_ladder_convex` — `E` is a strictly convex function of the bit width on
  the measured points (all ten triples of secant slopes are increasing), and
  `weight_ladder_strictAnti` — `E` is strictly decreasing in bit width.
* `scorecard_P1`, `scorecard_P2_refuted`, `scorecard_P3_refuted`,
  `q8_0_within_noise` — the pre-registered predictions, adjudicated.
* `geometric_closure` / `excess_le_of_bits_below` — the abstract reason a
  geometric band forbids a floor: a per-bit multiplicative bound propagates to a
  bound `m ^ k` after `k` further bits are removed, so degradation can never blow
  up at a finite bit width.
* `one_bit_below_q2k_stays_under_fifty_percent` — the conditional extrapolation:
  if the fitted upper rate `m = 3` persists below 2.6 bpw, then even at 1.6 bpw
  the relative excess is still under the `+50%` "undeployable" threshold.
-/

namespace Catalog.Novelty.WeightQuantFloor

/-! ## 1. The measured ladder -/

/-- One measured rung of the weight-quantisation ladder.  The bit width is stored
in *tenths of a bit* so that bit-width gaps are natural numbers. -/
structure Rung where
  /-- weight precision, in tenths of a bit per weight -/
  tenthBits : ℕ
  /-- measured perplexity on the held-out slice -/
  ppl : ℚ
deriving DecidableEq

/-- The fp16 control perplexity. -/
def fp16PPL : ℚ := 6.9825

/-- Excess perplexity of a rung over the fp16 control. -/
def excess (r : Rung) : ℚ := r.ppl - fp16PPL

/-- Relative excess perplexity (the `dPPL` column of the table). -/
def relExcess (r : Rung) : ℚ := excess r / fp16PPL

/-- `q8_0`, ≈8.5 bpw. -/
def q8_0 : Rung := ⟨85, 6.9781⟩
/-- `q6_k`, ≈6.6 bpw. -/
def q6_k : Rung := ⟨66, 7.0006⟩
/-- `q5_k_m`, ≈5.5 bpw. -/
def q5_k_m : Rung := ⟨55, 7.0427⟩
/-- `q4_k_m`, ≈4.8 bpw.  Its perplexity reproduced the NET-92 control exactly. -/
def q4_k_m : Rung := ⟨48, 7.1093⟩
/-- `q3_k_m`, ≈3.9 bpw. -/
def q3_k_m : Rung := ⟨39, 7.2758⟩
/-- `q2_k`, ≈2.6 bpw. -/
def q2_k : Rung := ⟨26, 8.1105⟩

/-- The calibration-aware k-quant ladder.  `q8_0` is excluded: its measured
perplexity is *below* the fp16 control, i.e. it is a noise-level rung
(`q8_0_within_noise`), so a multiplicative law cannot be tested against it. -/
def ladder : List Rung := [q6_k, q5_k_m, q4_k_m, q3_k_m, q2_k]


/-! ## 2. The one-parameter geometric law -/





/-! ## 3. The pre-registered scorecard -/






/-! ## 4. Why a geometric band forbids a floor -/




end Catalog.Novelty.WeightQuantFloor


