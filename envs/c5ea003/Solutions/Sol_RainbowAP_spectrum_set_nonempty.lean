-- Prove2me | solution 1 for RainbowAP.spectrum_set_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:23:51.835199+00:00
-- url     : https://prove2.me/submissions/e9f3c292-c74a-4e33-bd53-3f2d20f05596

-- Sol generated from Shared/RainbowAPSpectrumAsymptotics.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumThreshold
import Theorems.Thm_RainbowAP_majority_surjective_of
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
lemma solution(hN : 2 ≤ Fintype.card α) :
    {m | 2 * nonSurjCount α m < Fintype.card α ^ m}.Nonempty := by
  set N := Fintype.card α with hNdef
  refine ⟨⌊(N : ℝ) * Real.log (2 * (N : ℝ))⌋₊ + 1, ?_⟩
  apply majority_surjective_of
  apply two_mul_pow_lt_pow hN
  have h1 : (N : ℝ) * Real.log (2 * (N : ℝ))
      < (⌊(N : ℝ) * Real.log (2 * (N : ℝ))⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  push_cast
  linarith
