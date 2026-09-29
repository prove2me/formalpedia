-- Prove2me | Definitions.Def_Applications_DoppelgangerPhaseLock_Counting
-- name    : Applications_DoppelgangerPhaseLock_Counting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:42:20.660199+00:00
-- url     : https://prove2.me/theorems/0210c9f6-40ef-47df-bc90-d764c32f3130
-- title:
--   Aether Catalog definitions — Applications_DoppelgangerPhaseLock_Counting
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.DoppelgangerPhaseLock.Counting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/DoppelgangerPhaseLock/Counting.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
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

namespace Doppelganger

variable {S I : Type*}

/-- The stimulus word obtained by concatenating `m` blocks of length `L`. -/
def blockWord {L m : ℕ} (b : Fin m → (Fin L → I)) : List I :=
  (List.ofFn fun j => List.ofFn (b j)).flatten





end Doppelganger


