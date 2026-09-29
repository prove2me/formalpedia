-- Prove2me | solution 1 for Doppelganger.exists_short_merge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:51:38.67963+00:00
-- url     : https://prove2.me/submissions/e0c9da1e-f3b3-4b8d-8abf-1f6511e9b9a2

-- Sol generated from Applications/DoppelgangerPhaseLock/Finite.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Finite
import Theorems.Thm_Doppelganger_shorten_merge
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






open Doppelganger in
theorem solution[Fintype S] (δ : S → I → S) {s t : S} (h : Mergeable δ s t) :
    ∃ v : List I, v.length ≤ Fintype.card S * Fintype.card S ∧ drive δ v s = drive δ v t := by
  obtain ⟨w, hw⟩ := h
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    subst hn
    by_cases hle : w.length ≤ Fintype.card S * Fintype.card S
    · exact ⟨w, hle, hw⟩
    · obtain ⟨v, hvlen, hv⟩ := shorten_merge δ (by omega) hw
      exact ih v.length hvlen v hv rfl
