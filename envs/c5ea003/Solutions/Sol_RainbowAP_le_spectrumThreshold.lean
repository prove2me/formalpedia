-- Prove2me | solution 1 for RainbowAP.le_spectrumThreshold
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:25:08.961495+00:00
-- url     : https://prove2.me/submissions/3370245c-9287-4ba5-bb5e-61d323bfb720

-- Sol generated from Shared/RainbowAPSpectrumAsymptotics.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumThreshold
import Theorems.Thm_RainbowAP_majority_nonSurjective_of
import Theorems.Thm_RainbowAP_mem_of_spectrumThreshold
import Theorems.Thm_RainbowAP_pow_lt_succ_mul_pow_sub_one
import Theorems.Thm_RainbowAP_spectrum_set_nonempty

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
    ((Fintype.card α : ℝ) - 1) * Real.log ((Fintype.card α : ℝ) + 1)
      ≤ (spectrumThreshold α : ℝ) := by
  by_contra hcon
  push_neg at hcon
  have hmem := mem_of_spectrumThreshold (spectrum_set_nonempty (α := α) hN)
  have hcrit := majority_nonSurjective_of (α := α) (spectrumThreshold α) hN
    (pow_lt_succ_mul_pow_sub_one hN hcon)
  omega
