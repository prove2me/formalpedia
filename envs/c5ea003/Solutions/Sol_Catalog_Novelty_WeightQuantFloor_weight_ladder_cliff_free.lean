-- Prove2me | solution 1 for Catalog.Novelty.WeightQuantFloor.weight_ladder_cliff_free
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:32:07.780546+00:00
-- url     : https://prove2.me/submissions/b1089d48-0fe8-408a-838d-092deaca8706

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







/-- Every rung of the k-quant ladder degrades the model: `E > 0`. -/
theorem ladder_excess_pos {r : Rung} (hr : r ∈ ladder) : 0 < excess r := by
  fin_cases hr <;> norm_num [excess, fp16PPL, q6_k, q5_k_m, q4_k_m, q3_k_m, q2_k]

/-! ## 2. The one-parameter geometric law -/

/-- **The weight law.**  For every ordered pair of rungs of the k-quant ladder,
the excess perplexity is multiplied by a factor between `5/2` and `3` for each
bit of precision removed.  Stated without division: with `k` the gap in tenths of
a bit, `(5/2)^k · E(r)^10 ≤ E(s)^10 ≤ 3^k · E(r)^10`.

This is a genuine one-parameter fit: the same band covers all ten pairs, not just
the four adjacent ones, so `E(b) ≍ C · m^(-b)` with `m ∈ [5/2, 3]` describes the
entire measured range 6.6 → 2.6 bpw. -/
theorem weight_ladder_geometric_band {r s : Rung} (hr : r ∈ ladder) (hs : s ∈ ladder)
    (h : s.tenthBits < r.tenthBits) :
    (5 / 2 : ℚ) ^ (r.tenthBits - s.tenthBits) * excess r ^ 10 ≤ excess s ^ 10 ∧
      excess s ^ 10 ≤ 3 ^ (r.tenthBits - s.tenthBits) * excess r ^ 10 := by
  fin_cases hr <;> fin_cases hs <;>
    simp_all [excess, fp16PPL, q6_k, q5_k_m, q4_k_m, q3_k_m, q2_k] <;> norm_num




/-! ## 3. The pre-registered scorecard -/






/-! ## 4. Why a geometric band forbids a floor -/





open Catalog.Novelty.WeightQuantFloor in
theorem solution{r s : Rung} (hr : r ∈ ladder) (hs : s ∈ ladder)
    (h : s.tenthBits < r.tenthBits) :
    excess s ^ 10 < 4 ^ (r.tenthBits - s.tenthBits) * excess r ^ 10 := by
  have hband := (weight_ladder_geometric_band hr hs h).2
  have hpos : (0 : ℚ) < excess r ^ 10 := pow_pos (ladder_excess_pos hr) 10
  have hk : 0 < r.tenthBits - s.tenthBits := Nat.sub_pos_of_lt h
  have hlt : (3 : ℚ) ^ (r.tenthBits - s.tenthBits) < 4 ^ (r.tenthBits - s.tenthBits) :=
    pow_lt_pow_left₀ (by norm_num) (by norm_num) hk.ne'
  exact lt_of_le_of_lt hband (mul_lt_mul_of_pos_right hlt hpos)
