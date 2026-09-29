-- Prove2me | Theorems.Thm_Doppelganger_shorten_merge
-- name    : Doppelganger.shorten_merge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:39:25.804992+00:00
-- url     : https://prove2.me/theorems/7d754827-9af5-4df6-af43-ee6361242e18
-- title:
--   Pigeonhole in the pair automaton.
-- statement:
--   **Pigeonhole in the pair automaton.**  A merging word longer than `|S|²` contains a
--   repeated pair-state and can therefore be shortened.
--
--   ```lean
--   theorem Doppelganger.shorten_merge[Fintype S] (δ : S → I → S) {s t : S} {w : List I}
--       (hlen : Fintype.card S * Fintype.card S < w.length)
--       (hw : drive δ w s = drive δ w t) :
--       ∃ v : List I, v.length < w.length ∧ drive δ v s = drive δ v t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Finite.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Finite.lean#L182

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

theorem Doppelganger.shorten_merge[Fintype S] (δ : S → I → S) {s t : S} {w : List I}
    (hlen : Fintype.card S * Fintype.card S < w.length)
    (hw : drive δ w s = drive δ w t) :
    ∃ v : List I, v.length < w.length ∧ drive δ v s = drive δ v t := by sorry
