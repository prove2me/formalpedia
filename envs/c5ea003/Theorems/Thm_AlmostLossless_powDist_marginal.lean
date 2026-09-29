-- Prove2me | Theorems.Thm_AlmostLossless_powDist_marginal
-- name    : AlmostLossless.powDist_marginal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:05:39.86381+00:00
-- url     : https://prove2.me/theorems/610bc27a-cc21-4447-a21c-5ccabf1ddc31
-- title:
--   Exact marginalization.
-- statement:
--   **Exact marginalization.**  The mass of the event "block `j` lands in `B`"
--   under the product source is exactly the mass of `B` under the one-block
--   source.
--
--   ```lean
--   theorem AlmostLossless.powDist_marginal(μ : FinProbDist β) (b : ℕ) (j : Fin b) (B : Finset β) :
--       setMass (powDist μ b) (Finset.univ.filter (fun x : Fin b → β => x j ∈ B))
--         = setMass μ B := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessBlockDecoding.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessBlockDecoding.lean#L50

-- Thm stub generated from Bridges/AlmostLosslessBlockDecoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessBlockDecoding
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_MinEntropy
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

theorem AlmostLossless.powDist_marginal(μ : FinProbDist β) (b : ℕ) (j : Fin b) (B : Finset β) :
    setMass (powDist μ b) (Finset.univ.filter (fun x : Fin b → β => x j ∈ B))
      = setMass μ B := by sorry
