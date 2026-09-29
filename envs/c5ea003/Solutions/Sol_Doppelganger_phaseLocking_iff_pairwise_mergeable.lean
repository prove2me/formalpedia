-- Prove2me | solution 1 for Doppelganger.phaseLocking_iff_pairwise_mergeable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:51:39.933674+00:00
-- url     : https://prove2.me/submissions/9f48d0a1-2bc5-4e27-affb-e177e2b6e381

-- Sol generated from Applications/DoppelgangerPhaseLock/Finite.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Finite
import Theorems.Thm_Doppelganger_Locks_mergeable
import Theorems.Thm_Doppelganger_exists_lock_of_pairwise_mergeable
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
theorem solution[Fintype S] [Nonempty S] (δ : S → I → S) :
    PhaseLocking δ ↔ ∀ s t : S, Mergeable δ s t := by
  classical
  constructor
  · rintro ⟨w, hw⟩ s t
    exact hw.mergeable s t
  · intro h
    choose w hw using h
    set L := Finset.univ.sup (fun p : S × S => (w p.1 p.2).length) with hL
    have hbound : ∀ s t : S, ∃ v : List I, v.length ≤ L ∧ drive δ v s = drive δ v t := by
      intro s t
      refine ⟨w s t, ?_, hw s t⟩
      exact Finset.le_sup (f := fun p : S × S => (w p.1 p.2).length) (Finset.mem_univ (s, t))
    obtain ⟨v, _, hv⟩ := exists_lock_of_pairwise_mergeable δ L hbound
    exact ⟨v, hv⟩
