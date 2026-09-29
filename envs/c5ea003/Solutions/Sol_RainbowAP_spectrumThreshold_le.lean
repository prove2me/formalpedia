-- Prove2me | solution 1 for RainbowAP.spectrumThreshold_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:28:06.496794+00:00
-- url     : https://prove2.me/submissions/a86c7089-7aee-47c6-9064-6cc2b87a4154

-- Sol generated from Shared/RainbowAPSpectrumAsymptotics.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumThreshold
import Theorems.Thm_RainbowAP_majority_surjective_of
import Theorems.Thm_RainbowAP_spectrumThreshold_le_of_mem
import Theorems.Thm_RainbowAP_two_mul_pow_lt_pow

/-!
# Asymptotics of the full-spectrum threshold

We turn the two arithmetic criteria of `Shared.RainbowAPSpectrumThreshold` into real analytic
bounds, showing that for an alphabet with `N ≥ 2` letters

  `(N - 1) * log (N + 1) ≤ spectrumThreshold α ≤ N * log (2 N) + 1`.

Both sides are `N log N (1 + o(1))`, so the threshold is asymptotically `N log N`.
-/

open Finset Real

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]







open RainbowAP in
theorem solution(hN : 2 ≤ Fintype.card α) :
    (spectrumThreshold α : ℝ)
      ≤ (Fintype.card α : ℝ) * Real.log (2 * (Fintype.card α : ℝ)) + 1 := by
  set N := Fintype.card α with hNdef
  have hmem : spectrumThreshold α ≤ ⌊(N : ℝ) * Real.log (2 * (N : ℝ))⌋₊ + 1 := by
    apply spectrumThreshold_le_of_mem
    apply majority_surjective_of
    apply two_mul_pow_lt_pow hN
    have h1 : (N : ℝ) * Real.log (2 * (N : ℝ))
        < (⌊(N : ℝ) * Real.log (2 * (N : ℝ))⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    push_cast
    linarith
  have h2 : ((⌊(N : ℝ) * Real.log (2 * (N : ℝ))⌋₊ : ℝ))
      ≤ (N : ℝ) * Real.log (2 * (N : ℝ)) := by
    apply Nat.floor_le
    have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have : (1 : ℝ) ≤ 2 * (N : ℝ) := by linarith
    have := Real.log_nonneg this
    positivity
  have h3 : (spectrumThreshold α : ℝ) ≤ ((⌊(N : ℝ) * Real.log (2 * (N : ℝ))⌋₊ : ℝ)) + 1 := by
    exact_mod_cast hmem
  linarith
