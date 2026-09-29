-- Prove2me | Theorems.Thm_AlmostLossless_linear_lt_pow
-- name    : AlmostLossless.linear_lt_pow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:08:50.19681+00:00
-- url     : https://prove2.me/theorems/33ed16ce-50bd-4939-8c5a-e7f145cfa449
-- title:
--   Exponential separation.
-- statement:
--   **Exponential separation.**  For a codebook of size `n ≥ 2` and at least
--   three blocks, the coordinatewise decoder cost `b·n` is strictly smaller than the
--   one-shot cost `n^b` — and the ratio grows without bound.
--
--   ```lean
--   theorem AlmostLossless.linear_lt_pow{n b : ℕ} (hn : 2 ≤ n) (hb : 3 ≤ b) : b * n < n ^ b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessBlockDecoding.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessBlockDecoding.lean#L231

-- Thm stub generated from Bridges/AlmostLosslessBlockDecoding.lean
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

theorem AlmostLossless.linear_lt_pow{n b : ℕ} (hn : 2 ≤ n) (hb : 3 ≤ b) : b * n < n ^ b := by sorry
