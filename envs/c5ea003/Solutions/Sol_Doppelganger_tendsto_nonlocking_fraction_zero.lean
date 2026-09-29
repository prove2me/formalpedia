-- Prove2me | solution 1 for Doppelganger.tendsto_nonlocking_fraction_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:43:12.340964+00:00
-- url     : https://prove2.me/submissions/5d7491f6-237b-487a-9caa-dd145b6e383b

-- Sol generated from Applications/DoppelgangerPhaseLock/Counting.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Counting
import Theorems.Thm_Doppelganger_nonlocking_fraction_le
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
theorem solution[Fintype I] [Nonempty I] {δ : S → I → S} {L : ℕ}
    {u : Fin L → I} (hu : Locks δ (List.ofFn u)) (hq2 : 2 ≤ Fintype.card I ^ L) :
    Filter.Tendsto
      (fun m : ℕ => ((((Finset.univ : Finset (Fin m → (Fin L → I))).filter
        (fun b => ¬ Locks δ (blockWord b))).card : ℝ) / ((Fintype.card I ^ L : ℕ) : ℝ) ^ m))
      Filter.atTop (nhds 0) := by
  classical
  set q : ℕ := Fintype.card I ^ L with hqdef
  have hq0 : (0:ℝ) < (q : ℝ) := by
    have : (0:ℕ) < q := by omega
    exact_mod_cast this
  have hr0 : 0 ≤ 1 - ((q : ℝ))⁻¹ := by
    have : ((q : ℝ))⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      have : (1:ℕ) ≤ q := by omega
      exact_mod_cast this
    linarith
  have hr1 : 1 - ((q : ℝ))⁻¹ < 1 := by
    have : 0 < ((q : ℝ))⁻¹ := by positivity
    linarith
  refine squeeze_zero (fun m => by positivity) (fun m => nonlocking_fraction_le hu) ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
