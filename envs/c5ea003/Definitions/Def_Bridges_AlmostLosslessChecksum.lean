-- Prove2me | Definitions.Def_Bridges_AlmostLosslessChecksum
-- name    : Bridges_AlmostLosslessChecksum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:39.898786+00:00
-- url     : https://prove2.me/theorems/af2ee14e-8262-45c8-813a-a8ef24d98335
-- title:
--   Aether Catalog definitions — Bridges_AlmostLosslessChecksum
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlmostLosslessChecksum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlmostLosslessChecksum.lean by skeleton subtraction
import Mathlib
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

namespace AlmostLossless

section Pair

variable {α : Type*} [Fintype α] [DecidableEq α] {K K' M C : ℕ}

/-- Pair a hash family with a checksum family: `K·K'` keys, `M·C` codewords. -/
def pairHash (H : Fin K → α → Fin M) (G : Fin K' → α → Fin C) :
    Fin (K * K') → α → Fin (M * C) :=
  fun k x => finProdFinEquiv (H (finProdFinEquiv.symm k).1 x, G (finProdFinEquiv.symm k).2 x)





end Pair

end AlmostLossless


