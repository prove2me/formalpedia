-- Prove2me | solution 1 for Doppelganger.shorten_merge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:49:41.657285+00:00
-- url     : https://prove2.me/submissions/c3cc1740-51c5-400d-be14-1f205f3fd7b4

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
theorem solution[Fintype S] (δ : S → I → S) {s t : S} {w : List I}
    (hlen : Fintype.card S * Fintype.card S < w.length)
    (hw : drive δ w s = drive δ w t) :
    ∃ v : List I, v.length < w.length ∧ drive δ v s = drive δ v t := by
  classical
  set n := w.length with hn
  let f : Fin (n + 1) → S × S := fun k => (drive δ (w.take k) s, drive δ (w.take k) t)
  have hcard : Fintype.card (S × S) < Fintype.card (Fin (n + 1)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · refine ⟨w.take a ++ w.drop b, ?_, ?_⟩
    · have ha : (a : ℕ) ≤ n := by omega
      have hb : (b : ℕ) ≤ n := by omega
      simp only [List.length_append, List.length_take, List.length_drop, ← hn]
      omega
    · have key : ∀ x : S,
          drive δ (w.take a ++ w.drop b) x = drive δ (w.drop b) (drive δ (w.take a) x) :=
        fun x => drive_append δ _ _ x
      have hsplit : ∀ x : S, drive δ w x = drive δ (w.drop b) (drive δ (w.take b) x) := by
        intro x
        conv_lhs => rw [← List.take_append_drop (b : ℕ) w]
        exact drive_append δ _ _ x
      have h1 : drive δ (w.take a) s = drive δ (w.take b) s := congrArg Prod.fst hfab
      have h2 : drive δ (w.take a) t = drive δ (w.take b) t := congrArg Prod.snd hfab
      rw [key, key, h1, h2, ← hsplit, ← hsplit, hw]
  · refine ⟨w.take b ++ w.drop a, ?_, ?_⟩
    · have hba : (b : ℕ) < a := hlt
      have ha : (a : ℕ) ≤ n := by omega
      simp only [List.length_append, List.length_take, List.length_drop, ← hn]
      omega
    · have key : ∀ x : S,
          drive δ (w.take b ++ w.drop a) x = drive δ (w.drop a) (drive δ (w.take b) x) :=
        fun x => drive_append δ _ _ x
      have hsplit : ∀ x : S, drive δ w x = drive δ (w.drop a) (drive δ (w.take a) x) := by
        intro x
        conv_lhs => rw [← List.take_append_drop (a : ℕ) w]
        exact drive_append δ _ _ x
      have h1 : drive δ (w.take b) s = drive δ (w.take a) s := (congrArg Prod.fst hfab).symm
      have h2 : drive δ (w.take b) t = drive δ (w.take a) t := (congrArg Prod.snd hfab).symm
      rw [key, key, h1, h2, ← hsplit, ← hsplit, hw]
