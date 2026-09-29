-- Prove2me | Theorems.Thm_AlmostLossless_linHash_universal2
-- name    : AlmostLossless.linHash_universal2
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:08:23.637376+00:00
-- url     : https://prove2.me/theorems/09bc2cda-1d69-49c3-b114-7b8173b34d9d
-- title:
--   The inner-product family is 2-universal.
-- statement:
--   **The inner-product family is 2-universal.**  Distinct source symbols
--   collide for at most one key out of `p`; over a field this is the statement that
--   a nonzero linear equation in the key has a unique solution.
--
--   ```lean
--   theorem AlmostLossless.linHash_universal2: Universal2 (linHash p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessLinearHash.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessLinearHash.lean#L55

-- Thm stub generated from Bridges/AlmostLosslessLinearHash.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessLinearHash
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression IV: An Explicit 2-Universal Family

## Bridge: Finite fields (algebra) ↔ Shannon random coding (probability)

The achievability theorem of `AlmostLosslessRandomCoding` is stated for an
abstract 2-universal family.  This file removes any suspicion of vacuity by
exhibiting one: the **inner-product family** over a prime field,

  `h_k(x₁, x₂) = x₁ + k·x₂`  on  `(ZMod p)²`,  keyed by `k ∈ Fin p`.

It compresses a source of `p²` symbols into `p` codewords (half the raw rate),
and `linHash_universal2` proves the 2-universal property: two distinct source
symbols collide for **at most one** of the `p` keys.  Instantiating the general
theorem gives `exists_linear_almost_lossless`: a completely explicit
almost-lossless compressor with a proved failure bound and a proved decoding
cost.

## Impact: explicit_almost_lossless_code, certified_decoder_cost
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless


variable (p : ℕ) [Fact p.Prime]

theorem AlmostLossless.linHash_universal2: Universal2 (linHash p) := by sorry
