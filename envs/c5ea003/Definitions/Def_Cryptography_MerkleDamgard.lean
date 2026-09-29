-- Prove2me | Definitions.Def_Cryptography_MerkleDamgard
-- name    : Cryptography_MerkleDamgard
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:21:45.447563+00:00
-- url     : https://prove2.me/theorems/fd4f7361-c5f7-4f3d-aef2-7f2f1870ac2b
-- title:
--   Aether Catalog definitions — Cryptography_MerkleDamgard
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.MerkleDamgard`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/MerkleDamgard.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The Merkle–Damgård construction

The Merkle–Damgård transform builds a hash function on arbitrary block lists out
of a fixed-input-length compression function `f : State → Block → State`, by
iterating `f` from an initialization vector.

This file records two basic facts:

* `compression_collision_of_card` — a compression function that consumes at least
  one bit of input (`1 < #Block`) is *never* injective: by pigeonhole two distinct
  pairs `(s, b) ≠ (s', b')` collide.  This is the reason a fixed hash function can
  never be an injective extractor.
* `collision_extends` — the Merkle–Damgård transform is collision preserving: a
  collision in the compression function yields a collision of the full hash on
  block lists sharing a common suffix.
-/

namespace Cryptography.MerkleDamgard

variable {State Block : Type*}

/-- The Merkle–Damgård iterated hash: fold the compression function `f` over the
list of message blocks, starting from the state `iv`. -/
def hash (f : State → Block → State) (iv : State) : List Block → State
  | [] => iv
  | b :: bs => hash f (f iv b) bs







end Cryptography.MerkleDamgard


