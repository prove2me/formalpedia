-- Prove2me | Definitions.Def_Bridges_AlmostLosslessLinearHash
-- name    : Bridges_AlmostLosslessLinearHash
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:23.607985+00:00
-- url     : https://prove2.me/theorems/2a3ae595-f8d1-4531-ba4a-1305339b4bce
-- title:
--   Aether Catalog definitions — Bridges_AlmostLosslessLinearHash
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlmostLosslessLinearHash`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlmostLosslessLinearHash.lean by skeleton subtraction
import Mathlib
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

namespace AlmostLossless

section LinearHash

variable (p : ℕ) [Fact p.Prime]

/-- The field element attached to a key index. -/
def keyVal (k : Fin p) : ZMod p := (k.val : ZMod p)


/-- The inner-product hash family `h_k(x₁,x₂) = x₁ + k·x₂` over `ZMod p`. -/
def linHash (k : Fin p) (x : ZMod p × ZMod p) : Fin p :=
  ⟨(x.1 + keyVal p k * x.2).val, ZMod.val_lt _⟩





end LinearHash

/-! ## A concrete instance with explicit figures -/

section Concrete

instance : Fact (Nat.Prime 101) := ⟨by norm_num⟩



end Concrete

end AlmostLossless


