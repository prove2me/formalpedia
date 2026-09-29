-- Prove2me | Theorems.Thm_Cryptography_MerkleDamgard_compression_collision_of_card
-- name    : Cryptography.MerkleDamgard.compression_collision_of_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:44:51.557427+00:00
-- url     : https://prove2.me/theorems/e84db235-77bd-43b9-a2f0-1953a2725c6c
-- title:
--   Pigeonhole collision.
-- statement:
--   **Pigeonhole collision.**  A compression function `f : State → Block → State`
--   whose block alphabet has more than one element is never injective: there are two
--   distinct pairs with the same image.
--
--   ```lean
--   theorem Cryptography.MerkleDamgard.compression_collision_of_card[Fintype State] [Fintype Block] [Nonempty State]
--       (hB : 1 < Fintype.card Block) (f : State → Block → State) :
--       ∃ (s : State) (b : Block) (s' : State) (b' : Block),
--         (s, b) ≠ (s', b') ∧ f s b = f s' b' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MerkleDamgard.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MerkleDamgard.lean#L48

-- Thm stub generated from Cryptography/MerkleDamgard.lean
import Mathlib
import Definitions.Def_Cryptography_MerkleDamgard
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

open Cryptography.MerkleDamgard

variable {State Block : Type*}

theorem Cryptography.MerkleDamgard.compression_collision_of_card[Fintype State] [Fintype Block] [Nonempty State]
    (hB : 1 < Fintype.card Block) (f : State → Block → State) :
    ∃ (s : State) (b : Block) (s' : State) (b' : Block),
      (s, b) ≠ (s', b') ∧ f s b = f s' b' := by sorry
