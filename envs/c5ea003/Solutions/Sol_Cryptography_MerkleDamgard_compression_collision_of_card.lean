-- Prove2me | solution 1 for Cryptography.MerkleDamgard.compression_collision_of_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:58:11.272151+00:00
-- url     : https://prove2.me/submissions/e89b3740-d38d-481d-bc8f-56d20e7e629e

-- Sol generated from Cryptography/MerkleDamgard.lean
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









open Cryptography.MerkleDamgard in
theorem solution[Fintype State] [Fintype Block] [Nonempty State]
    (hB : 1 < Fintype.card Block) (f : State → Block → State) :
    ∃ (s : State) (b : Block) (s' : State) (b' : Block),
      (s, b) ≠ (s', b') ∧ f s b = f s' b' := by
  have hcard : Fintype.card State < Fintype.card (State × Block) := by
    rw [Fintype.card_prod]
    have hS : 0 < Fintype.card State := Fintype.card_pos
    nlinarith [hS, hB]
  obtain ⟨x, y, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun sb : State × Block => f sb.1 sb.2) hcard
  exact ⟨x.1, x.2, y.1, y.2, by simpa using hne, heq⟩
