-- Prove2me | solution 1 for Doppelganger.card_nonlocking_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:28:20.669743+00:00
-- url     : https://prove2.me/submissions/461ff777-c039-4624-b95c-07e4b0a88fe6

-- Sol generated from Applications/DoppelgangerPhaseLock/Counting.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Counting
import Theorems.Thm_Doppelganger_Locks_flatten_of_mem
/-
# Doppelgänger Phase-Lock — how *typical* is telepathy?

The synchronization theorem tells us that a locking stimulus word exists.  This file
answers the quantitative question an experimenter would ask: *if the environment supplies
stimuli blindly, how likely is it that the two separated agents phase-lock?*

We slice a stimulus stream of length `L * m` into `m` blocks of length `L`, where `L` is
the length of one locking block `u`.  Because locking words form a two-sided ideal
(`Doppelganger.locks_ideal`), a stream locks as soon as **one** of its blocks equals `u`.
Hence non-locking stream-prefixes must avoid `u` in every block, and a direct count gives

`#{non-locking block sequences} ≤ (|I|^L - 1)^m`,

out of `(|I|^L)^m` sequences overall: the failure fraction decays *geometrically*.  So
doppelgänger phase-lock is not a miracle but a probability-one event under blind
environmental driving.

## Main results

* `Doppelganger.locks_blockWord` — one locking block suffices.
* `Doppelganger.card_nonlocking_le` — the exact counting bound `(|I|^L - 1)^m`.
* `Doppelganger.nonlocking_fraction_le` — the failure fraction is `≤ (1 - |I|^{-L})^m`.
* `Doppelganger.tendsto_nonlocking_fraction_zero` — blind driving locks the doppelgängers
  with asymptotic probability one.
-/

open Doppelganger

variable {S I : Type*}


/-- **One locking block suffices.**  If some block of the stream is the locking block `u`,
the whole stream locks. -/
lemma locks_blockWord {δ : S → I → S} {L m : ℕ} {u : Fin L → I}
    (hu : Locks δ (List.ofFn u)) (b : Fin m → (Fin L → I)) (j : Fin m) (hj : b j = u) :
    Locks δ (blockWord b) := by
  refine Locks.flatten_of_mem δ ?_ hu
  rw [List.mem_ofFn]
  exact ⟨j, by rw [hj]⟩





open Doppelganger in
open Classical in
theorem solution[Fintype I] {δ : S → I → S} {L m : ℕ} {u : Fin L → I}
    (hu : Locks δ (List.ofFn u)) :
    ((Finset.univ : Finset (Fin m → (Fin L → I))).filter
      (fun b => ¬ Locks δ (blockWord b))).card ≤ (Fintype.card I ^ L - 1) ^ m := by
  classical
  have hsub : ((Finset.univ : Finset (Fin m → (Fin L → I))).filter
      (fun b => ¬ Locks δ (blockWord b)))
      ⊆ Fintype.piFinset (fun _ : Fin m => (Finset.univ : Finset (Fin L → I)).erase u) := by
    intro b hb
    simp only [Finset.mem_filter] at hb
    rw [Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_erase]
    refine ⟨fun hbj => hb.2 (locks_blockWord hu b j hbj), Finset.mem_univ _⟩
  calc _ ≤ (Fintype.piFinset
              (fun _ : Fin m => (Finset.univ : Finset (Fin L → I)).erase u)).card :=
        Finset.card_le_card hsub
    _ = (Fintype.card I ^ L - 1) ^ m := by
        rw [Fintype.card_piFinset]
        simp [Finset.card_erase_of_mem, Finset.card_univ]
