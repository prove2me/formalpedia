-- Prove2me | Theorems.Thm_Doppelganger_tendsto_nonlocking_fraction_zero
-- name    : Doppelganger.tendsto_nonlocking_fraction_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:42:24.671231+00:00
-- url     : https://prove2.me/theorems/2ef734ad-401c-4eb4-85b5-774ced3a39d9
-- title:
--   Blind driving synchronizes the doppelgängers almost surely.
-- statement:
--   **Blind driving synchronizes the doppelgängers almost surely.**  As the number of
--   observed blocks grows, the fraction of stimulus streams that fail to phase-lock tends to
--   zero, provided the environment offers at least two distinguishable stimuli in a block.
--
--   ```lean
--   theorem Doppelganger.tendsto_nonlocking_fraction_zero[Fintype I] [Nonempty I] {δ : S → I → S} {L : ℕ}
--       {u : Fin L → I} (hu : Locks δ (List.ofFn u)) (hq2 : 2 ≤ Fintype.card I ^ L) :
--       Filter.Tendsto
--         (fun m : ℕ => ((((Finset.univ : Finset (Fin m → (Fin L → I))).filter
--           (fun b => ¬ Locks δ (blockWord b))).card : ℝ) / ((Fintype.card I ^ L : ℕ) : ℝ) ^ m))
--         Filter.atTop (nhds 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Counting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Counting.lean#L99

-- Thm stub generated from Applications/DoppelgangerPhaseLock/Counting.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Counting
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





open Classical in

theorem Doppelganger.tendsto_nonlocking_fraction_zero[Fintype I] [Nonempty I] {δ : S → I → S} {L : ℕ}
    {u : Fin L → I} (hu : Locks δ (List.ofFn u)) (hq2 : 2 ≤ Fintype.card I ^ L) :
    Filter.Tendsto
      (fun m : ℕ => ((((Finset.univ : Finset (Fin m → (Fin L → I))).filter
        (fun b => ¬ Locks δ (blockWord b))).card : ℝ) / ((Fintype.card I ^ L : ℕ) : ℝ) ^ m))
      Filter.atTop (nhds 0) := by sorry
