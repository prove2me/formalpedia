-- Prove2me | solution 1 for AlmostLossless.linear_lt_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:19:29.387678+00:00
-- url     : https://prove2.me/submissions/6d4d512c-e2eb-43b5-ac33-64ad055321b6

-- Sol generated from Bridges/AlmostLosslessBlockDecoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessBlockDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression III: Beating the Exponential Decoder

## Bridge: Product measures (probability) ↔ Verified algorithm cost (computation)

The naive random-coding decoder of `AlmostLosslessRandomCoding` scans the whole
codebook.  On a block source `β^b` with a typical set `T^b` the codebook has
`|T|^b` entries, so decoding is *exponential in the block length*.

This file removes that obstacle.  We decode **coordinatewise**: each of the `b`
blocks gets its own unique-match scan over the size-`|T|` codebook, and the
answers are assembled.  The results:

* `powDist_marginal` — exact marginalization for the `b`-fold product source;
* `setMass_powDist_exists_le` — a union bound over blocks for the product source;
* `blockDec_eq_some_iff` — the block decoder is *exactly* the coordinatewise
  decoder, so it never corrupts silently on the product codebook;
* `blockScheme_failure_bound` — failure probability `≤ b · (per-block failure)`;
* `blockScanCost_eq_sum` / `blockScanCost_const` — cost is exactly `b·|T|`
  hash evaluations, versus `|T|^b` for the naive scan
  (`naive_codebook_card`), and `linear_lt_pow` shows the gap is genuine.

## Impact: polynomial_time_random_coding, certified_decoder_cost
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless

/-! ## Section 1: The `b`-fold product source -/


variable {β : Type*} [Fintype β] [DecidableEq β]





/-! ## Section 2: The coordinatewise (block) decoder -/


variable {β : Type*} [Fintype β] [DecidableEq β] {b m : ℕ}







/-! ## Section 3: Failure probability of the block scheme -/


/-! ## Section 4: Exact decoding cost, and the exponential separation -/








/-! ## Section 5: The full block scheme with a universal hash family -/


variable {β : Type*} [Fintype β] [DecidableEq β] {K m : ℕ}




open AlmostLossless in
theorem solution{n b : ℕ} (hn : 2 ≤ n) (hb : 3 ≤ b) : b * n < n ^ b := by
  induction b, hb using Nat.le_induction with
  | base =>
      have h1 : 3 * n < n ^ 3 := by nlinarith [sq_nonneg n]
      simpa using h1
  | succ b hb ih =>
      have hpow : 2 ≤ n ^ b := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ n ^ b := Nat.pow_le_pow_left hn b
      have hstep : n ^ b + n ≤ n ^ (b + 1) := by
        have : n ^ (b + 1) = n ^ b * n := by ring
        rw [this]
        nlinarith [hpow, hn]
      calc (b + 1) * n = b * n + n := by ring
        _ < n ^ b + n := by omega
        _ ≤ n ^ (b + 1) := hstep
