-- Prove2me | solution 1 for Doppelganger.exists_lock_of_pairwise_mergeable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:49:41.055038+00:00
-- url     : https://prove2.me/submissions/5628cee1-d4cc-4232-80d2-bcfd651321d2

-- Sol generated from Applications/DoppelgangerPhaseLock/Finite.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Finite
import Theorems.Thm_Doppelganger_exists_word_image_card_eq_one
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
theorem solution[Fintype S] [Nonempty S] (δ : S → I → S) (L : ℕ)
    (h : ∀ s t : S, ∃ w : List I, w.length ≤ L ∧ drive δ w s = drive δ w t) :
    ∃ w : List I, w.length ≤ (Fintype.card S - 1) * L ∧ Locks δ w := by
  obtain ⟨w, hlen, hcard⟩ :=
    exists_word_image_card_eq_one δ L h (Fintype.card S) Finset.univ
      (by simp [Finset.card_univ]) Finset.univ_nonempty
  refine ⟨w, by simpa [Finset.card_univ] using hlen, fun s t => ?_⟩
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
  have hs : drive δ w s ∈ Finset.univ.image (drive δ w) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ s)
  have ht : drive δ w t ∈ Finset.univ.image (drive δ w) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ t)
  rw [hc] at hs ht
  simp only [Finset.mem_singleton] at hs ht
  rw [hs, ht]
