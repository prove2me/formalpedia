-- Prove2me | Theorems.Thm_Doppelganger_exists_lock_length_le_of_phaseLocking
-- name    : Doppelganger.exists_lock_length_le_of_phaseLocking
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:39:40.039684+00:00
-- url     : https://prove2.me/theorems/24b59d23-c2c0-4890-8116-3bdb8389699f
-- title:
--   Unconditional phase-lock time bound.
-- statement:
--   **Unconditional phase-lock time bound.**  A finite agent that admits doppelgänger
--   phase-lock at all admits it within `(|S| - 1) · |S|²` stimuli.
--
--   ```lean
--   theorem Doppelganger.exists_lock_length_le_of_phaseLocking[Fintype S] [Nonempty S] [DecidableEq S]
--       (δ : S → I → S) (h : PhaseLocking δ) :
--       ∃ w : List I,
--         w.length ≤ (Fintype.card S - 1) * (Fintype.card S * Fintype.card S) ∧ Locks δ w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Finite.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Finite.lean#L239

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







/-! ### An absolute (Černý-style) bound on the phase-lock time

So far the locking time was expressed in terms of an *assumed* bound `L` on pairwise
merging times.  We now remove that assumption: a pigeonhole argument in the **pair
automaton** `S × S` shows that a mergeable pair is always mergeable within `|S|²`
stimuli, whence an unconditional cubic bound on the doppelgänger phase-lock time.
-/

theorem Doppelganger.exists_lock_length_le_of_phaseLocking[Fintype S] [Nonempty S] [DecidableEq S]
    (δ : S → I → S) (h : PhaseLocking δ) :
    ∃ w : List I,
      w.length ≤ (Fintype.card S - 1) * (Fintype.card S * Fintype.card S) ∧ Locks δ w := by sorry
