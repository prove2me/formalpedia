-- Prove2me | solution 1 for Catalog.Novelty.WeightQuantFloor.geometric_closure
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:32:07.080704+00:00
-- url     : https://prove2.me/submissions/66b0fc77-7008-4afb-a4dc-1511caced6c5

-- Sol generated from Novelty/WeightQuantFloorLadder.lean
import Mathlib
import Definitions.Def_Novelty_WeightQuantFloorLadder

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

open Catalog.Novelty.WeightQuantFloor

/-! ## 1. The measured ladder -/








/-! ## 2. The one-parameter geometric law -/





/-! ## 3. The pre-registered scorecard -/






/-! ## 4. Why a geometric band forbids a floor -/





open Catalog.Novelty.WeightQuantFloor in
theorem solution(D : ℕ → ℝ) (m : ℝ) (hm : 0 ≤ m)
    (hstep : ∀ b, D b ≤ m * D (b + 10)) :
    ∀ b k, D b ≤ m ^ k * D (b + 10 * k) := by
  intro b k
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : D (b + 10 * k) ≤ m * D (b + 10 * (k + 1)) := by
        have := hstep (b + 10 * k)
        have hidx : b + 10 * k + 10 = b + 10 * (k + 1) := by ring
        rwa [hidx] at this
      have h2 : m ^ k * D (b + 10 * k) ≤ m ^ k * (m * D (b + 10 * (k + 1))) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hm k)
      calc D b ≤ m ^ k * D (b + 10 * k) := ih
        _ ≤ m ^ k * (m * D (b + 10 * (k + 1))) := h2
        _ = m ^ (k + 1) * D (b + 10 * (k + 1)) := by ring
