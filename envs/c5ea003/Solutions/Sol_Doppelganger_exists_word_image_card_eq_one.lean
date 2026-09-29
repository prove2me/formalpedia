-- Prove2me | solution 1 for Doppelganger.exists_word_image_card_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T23:25:19.278989+00:00
-- url     : https://prove2.me/submissions/b8311791-2766-4411-af87-9fbc79212a49

-- Sol generated from Applications/DoppelgangerPhaseLock/Finite.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Finite
import Theorems.Thm_Doppelganger_card_image_lt_of_collision
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
theorem solution(δ : S → I → S) (L : ℕ)
    (h : ∀ s t : S, ∃ w : List I, w.length ≤ L ∧ drive δ w s = drive δ w t) :
    ∀ (n : ℕ) (A : Finset S), A.card ≤ n → A.Nonempty →
      ∃ w : List I, w.length ≤ (A.card - 1) * L ∧ (A.image (drive δ w)).card = 1 := by
  intro n
  induction n with
  | zero => intro A hA hne; exact absurd (Finset.card_pos.mpr hne) (by omega)
  | succ n ih =>
    intro A hcard hne
    by_cases h1 : A.card = 1
    · refine ⟨[], by simp, ?_⟩
      have himg : A.image (drive δ ([] : List I)) = A := by
        simp only [show (drive δ ([] : List I)) = id from rfl, Finset.image_id]
      rw [himg]; exact h1
    · have h2 : 1 < A.card := by
        have := Finset.card_pos.mpr hne; omega
      obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp h2
      obtain ⟨v, hvlen, hv⟩ := h s t
      set B := A.image (drive δ v) with hB
      have hBlt : B.card < A.card := card_image_lt_of_collision _ hs ht hst hv
      have hBne : B.Nonempty := hne.image _
      obtain ⟨u, hulen, hu⟩ := ih B (by omega) hBne
      refine ⟨v ++ u, ?_, ?_⟩
      · have hlen : (v ++ u).length ≤ L + (B.card - 1) * L := by
          simpa using Nat.add_le_add hvlen hulen
        refine hlen.trans ?_
        calc L + (B.card - 1) * L = (B.card - 1 + 1) * L := by ring
          _ ≤ (A.card - 1) * L := Nat.mul_le_mul_right _ (by omega)
      · rw [show A.image (drive δ (v ++ u)) = B.image (drive δ u) by
          rw [hB, Finset.image_image]; congr 1; funext x; exact drive_append δ v u x]
        exact hu
