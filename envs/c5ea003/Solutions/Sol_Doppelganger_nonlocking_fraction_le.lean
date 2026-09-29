-- Prove2me | solution 1 for Doppelganger.nonlocking_fraction_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:40:38.03906+00:00
-- url     : https://prove2.me/submissions/e2e0cd8c-f1b8-475d-bdb6-d1a378b0cb92

-- Sol generated from Applications/DoppelgangerPhaseLock/Counting.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Counting
import Theorems.Thm_Doppelganger_card_nonlocking_le
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







open Doppelganger in
open Classical in
theorem solution[Fintype I] [Nonempty I] {δ : S → I → S} {L m : ℕ}
    {u : Fin L → I} (hu : Locks δ (List.ofFn u)) :
    ((((Finset.univ : Finset (Fin m → (Fin L → I))).filter
        (fun b => ¬ Locks δ (blockWord b))).card : ℝ) / ((Fintype.card I ^ L : ℕ) : ℝ) ^ m)
      ≤ (1 - (((Fintype.card I ^ L : ℕ) : ℝ))⁻¹) ^ m := by
  classical
  set q : ℕ := Fintype.card I ^ L with hqdef
  have hq : 1 ≤ q := Nat.one_le_pow _ _ Fintype.card_pos
  have hq0 : (0:ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    push_cast [Nat.cast_sub hq]; ring
  have hc : (((Finset.univ : Finset (Fin m → (Fin L → I))).filter
      (fun b => ¬ Locks δ (blockWord b))).card : ℝ) ≤ ((q : ℝ) - 1) ^ m := by
    calc (((Finset.univ : Finset (Fin m → (Fin L → I))).filter
            (fun b => ¬ Locks δ (blockWord b))).card : ℝ)
          ≤ (((q - 1) ^ m : ℕ) : ℝ) := by exact_mod_cast card_nonlocking_le hu
      _ = ((q : ℝ) - 1) ^ m := by push_cast [hcast]; ring
  calc (((Finset.univ : Finset (Fin m → (Fin L → I))).filter
        (fun b => ¬ Locks δ (blockWord b))).card : ℝ) / (q : ℝ) ^ m
      ≤ ((q : ℝ) - 1) ^ m / (q : ℝ) ^ m := by gcongr
    _ = (1 - ((q : ℝ))⁻¹) ^ m := by
        rw [← div_pow]
        congr 1
        field_simp
