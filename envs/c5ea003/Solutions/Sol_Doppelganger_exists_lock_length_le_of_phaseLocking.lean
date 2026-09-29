-- Prove2me | solution 1 for Doppelganger.exists_lock_length_le_of_phaseLocking
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:53:53.250806+00:00
-- url     : https://prove2.me/submissions/41411452-ec7f-4dcb-b5bf-30735e699fa5

-- Sol generated from Applications/DoppelgangerPhaseLock/Finite.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Finite
import Theorems.Thm_Doppelganger_exists_lock_of_pairwise_mergeable
import Theorems.Thm_Doppelganger_exists_short_merge
import Theorems.Thm_Doppelganger_phaseLocking_iff_pairwise_mergeable
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
theorem solution[Fintype S] [Nonempty S] [DecidableEq S]
    (δ : S → I → S) (h : PhaseLocking δ) :
    ∃ w : List I,
      w.length ≤ (Fintype.card S - 1) * (Fintype.card S * Fintype.card S) ∧ Locks δ w := by
  have hpair : ∀ s t : S, ∃ v : List I,
      v.length ≤ Fintype.card S * Fintype.card S ∧ drive δ v s = drive δ v t := by
    intro s t
    exact exists_short_merge δ (((phaseLocking_iff_pairwise_mergeable δ).mp h) s t)
  exact exists_lock_of_pairwise_mergeable δ _ hpair
