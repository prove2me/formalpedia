-- Prove2me | Theorems.Thm_AlmostLossless_blockDec_eq_some_iff
-- name    : AlmostLossless.blockDec_eq_some_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:05:13.134091+00:00
-- url     : https://prove2.me/theorems/a42c9a8c-0c88-4645-94ea-9523fd03f085
-- title:
--   The block decoder is *exactly* the coordinatewise decoder.
-- statement:
--   The block decoder is *exactly* the coordinatewise decoder.
--
--   ```lean
--   theorem AlmostLossless.blockDec_eq_some_iff{l : Fin b → List β} {h : Fin b → β → Fin m}
--       {c : Fin b → Fin m} {x : Fin b → β} :
--       blockDec l h c = some x ↔ ∀ j, decodeList (h j) (l j) (c j) = some (x j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessBlockDecoding.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessBlockDecoding.lean#L132

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




omit [Fintype β] [DecidableEq β] in

theorem AlmostLossless.blockDec_eq_some_iff{l : Fin b → List β} {h : Fin b → β → Fin m}
    {c : Fin b → Fin m} {x : Fin b → β} :
    blockDec l h c = some x ↔ ∀ j, decodeList (h j) (l j) (c j) = some (x j) := by sorry
