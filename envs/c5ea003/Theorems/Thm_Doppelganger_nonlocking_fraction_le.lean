-- Prove2me | Theorems.Thm_Doppelganger_nonlocking_fraction_le
-- name    : Doppelganger.nonlocking_fraction_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:42:13.388917+00:00
-- url     : https://prove2.me/theorems/39eb2747-a2f2-4008-b079-8ffb5bac2847
-- title:
--   Geometric decay of the failure fraction.
-- statement:
--   **Geometric decay of the failure fraction.**  Writing `q = |I|^L` for the number of
--   possible blocks, the proportion of length-`L·m` stimulus streams that fail to phase-lock
--   the two agents is at most `(1 - 1/q)^m`.
--
--   ```lean
--   theorem Doppelganger.nonlocking_fraction_le[Fintype I] [Nonempty I] {δ : S → I → S} {L m : ℕ}
--       {u : Fin L → I} (hu : Locks δ (List.ofFn u)) :
--       ((((Finset.univ : Finset (Fin m → (Fin L → I))).filter
--           (fun b => ¬ Locks δ (blockWord b))).card : ℝ) / ((Fintype.card I ^ L : ℕ) : ℝ) ^ m)
--         ≤ (1 - (((Fintype.card I ^ L : ℕ) : ℝ))⁻¹) ^ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Counting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Counting.lean#L70

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

theorem Doppelganger.nonlocking_fraction_le[Fintype I] [Nonempty I] {δ : S → I → S} {L m : ℕ}
    {u : Fin L → I} (hu : Locks δ (List.ofFn u)) :
    ((((Finset.univ : Finset (Fin m → (Fin L → I))).filter
        (fun b => ¬ Locks δ (blockWord b))).card : ℝ) / ((Fintype.card I ^ L : ℕ) : ℝ) ^ m)
      ≤ (1 - (((Fintype.card I ^ L : ℕ) : ℝ))⁻¹) ^ m := by sorry
