-- Prove2me | Theorems.Thm_Doppelganger_card_image_lt_of_collision
-- name    : Doppelganger.card_image_lt_of_collision
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:38:02.046854+00:00
-- url     : https://prove2.me/theorems/04e15b91-a141-4d08-b7c3-b9102e831ab3
-- title:
--   A collision inside a finite set strictly drops the cardinality of its image.
-- statement:
--   A collision inside a finite set strictly drops the cardinality of its image.
--
--   ```lean
--   theorem Doppelganger.card_image_lt_of_collision(f : S → S) {A : Finset S} {s t : S} (hs : s ∈ A)
--       (ht : t ∈ A) (hst : s ≠ t) (hf : f s = f t) : (A.image f).card < A.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Finite.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Finite.lean#L81

-- Thm stub generated from Applications/DoppelgangerPhaseLock/Finite.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Finite
/-
# Doppelgänger Phase-Lock — the finite-state synchronization theorem

This file proves the central structural theorem of the theme: for a **finite** state
space, *pairwise* telepathy implies *global* telepathy.  In other words, if any two
individual internal states of the agent can be merged by *some* stimulus word, then a
single universal stimulus word merges **all** states simultaneously — the two
spatially separated doppelgängers phase-lock no matter how they started.

The proof is a greedy image-collapsing (Černý-style) argument, and it is quantitative:
if every pair can be merged by a word of length `≤ L`, a universal locking word of
length `≤ (|S| - 1) * L` exists.

## Main results

* `Doppelganger.rank_append_le` — the *rank* (image cardinality) of a stimulus word is
  antitone under extension: information is only ever destroyed.
* `Doppelganger.locks_iff_rank_eq_one` — locking words are exactly the rank-one words.
* `Doppelganger.exists_lock_of_pairwise_mergeable` — the quantitative synchronization
  theorem (Černý form).
* `Doppelganger.phaseLocking_iff_pairwise_mergeable` — pairwise ⟺ global phase-lock.
-/

open Doppelganger

variable {S I : Type*}


variable [Fintype S] [DecidableEq S]







variable [DecidableEq S]

theorem Doppelganger.card_image_lt_of_collision(f : S → S) {A : Finset S} {s t : S} (hs : s ∈ A)
    (ht : t ∈ A) (hst : s ≠ t) (hf : f s = f t) : (A.image f).card < A.card := by sorry
