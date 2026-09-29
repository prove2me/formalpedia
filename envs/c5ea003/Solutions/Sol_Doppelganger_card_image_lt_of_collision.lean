-- Prove2me | solution 1 for Doppelganger.card_image_lt_of_collision
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:39:55.103988+00:00
-- url     : https://prove2.me/submissions/ff919b44-eb17-43e7-ba0d-72187e4b1442

-- Sol generated from Applications/DoppelgangerPhaseLock/Finite.lean
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






open Doppelganger in
theorem solution(f : S → S) {A : Finset S} {s t : S} (hs : s ∈ A)
    (ht : t ∈ A) (hst : s ≠ t) (hf : f s = f t) : (A.image f).card < A.card := by
  have hsub : A.image f = (A.erase s).image f := by
    apply Finset.Subset.antisymm
    · intro y hy
      simp only [Finset.mem_image] at hy ⊢
      obtain ⟨x, hx, rfl⟩ := hy
      by_cases hxs : x = s
      · exact ⟨t, Finset.mem_erase.mpr ⟨Ne.symm hst, ht⟩, by rw [hxs, hf]⟩
      · exact ⟨x, Finset.mem_erase.mpr ⟨hxs, hx⟩, rfl⟩
    · exact Finset.image_subset_image (Finset.erase_subset _ _)
  calc (A.image f).card = ((A.erase s).image f).card := by rw [hsub]
    _ ≤ (A.erase s).card := Finset.card_image_le
    _ < A.card := Finset.card_erase_lt_of_mem hs
