-- Prove2me | Theorems.Thm_AlmostLossless_pairHash_universal2
-- name    : AlmostLossless.pairHash_universal2
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:08:28.045072+00:00
-- url     : https://prove2.me/theorems/6b5a1b47-268d-4012-ac25-906cb0c6c09b
-- title:
--   2-universality is multiplicative under pairing.
-- statement:
--   **2-universality is multiplicative under pairing.**  A `1/M`-universal hash
--   composed with a `1/C`-universal checksum is a `1/(M·C)`-universal family.
--
--   ```lean
--   theorem AlmostLossless.pairHash_universal2{H : Fin K → α → Fin M} {G : Fin K' → α → Fin C}
--       (hH : Universal2 H) (hG : Universal2 G) : Universal2 (pairHash H G) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessChecksum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessChecksum.lean#L51

-- Thm stub generated from Bridges/AlmostLosslessChecksum.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessChecksum
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression V: Checksums and Guaranteed Error Detection

## Bridge: Product constructions (combinatorics) ↔ Error detection (coding theory)

`AlmostLosslessRandomCoding` shows that a codebook symbol is *never* corrupted
silently, and that an off-codebook symbol is corrupted with probability at most
`|S|/M`.  A **checksum** is the standard way to push the latter down without
redesigning the code: append `log C` extra bits computed by a second,
independent universal family.

The structural fact that makes this work is that 2-universality is closed under
pairing, with the collision parameter *multiplying*:

  `pairHash_universal2 : Universal2 H → Universal2 G → Universal2 (H ⊗ G)`

where `H ⊗ G` has `K·K'` keys and `M·C` codewords.  Feeding this into the main
achievability theorem gives `exists_checksummed_scheme`: silent corruption below
any target `η`, at an additive cost of `log C` bits.

## Impact: guaranteed_error_detection, no_silent_corruption
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless


variable {α : Type*} [Fintype α] [DecidableEq α] {K K' M C : ℕ}



omit [Fintype α] [DecidableEq α] in

theorem AlmostLossless.pairHash_universal2{H : Fin K → α → Fin M} {G : Fin K' → α → Fin C}
    (hH : Universal2 H) (hG : Universal2 G) : Universal2 (pairHash H G) := by sorry
