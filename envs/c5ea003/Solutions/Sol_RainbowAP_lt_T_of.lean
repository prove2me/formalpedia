-- Prove2me | solution 1 for RainbowAP.lt_T_of
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:19:08.636321+00:00
-- url     : https://prove2.me/submissions/eca5ac18-0050-4068-b536-19839f0e0316

-- Sol generated from Shared/RainbowAPSmallCases.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPMonotone
import Definitions.Def_Shared_RainbowAPPairThreshold
import Definitions.Def_Shared_RainbowAPSpectrumThreshold
import Theorems.Thm_RainbowAP_card_pair_alphabet
import Theorems.Thm_RainbowAP_card_pair_alphabet_ge
import Theorems.Thm_RainbowAP_majority_iff_threshold_le
import Theorems.Thm_RainbowAP_majority_nonSurjective_of
import Theorems.Thm_RainbowAP_spectrum_set_nonempty

/-!
# Verified small cases of the rainbow pair-spectrum threshold

Combining the two majority criteria with the monotonicity of the transition
(`RainbowAP.majority_iff_threshold_le`) pins `T k` inside an explicit integer window for each
small `k`.  These windows are computed here by pure numeral arithmetic; they agree with the exact
values `T 2 = 7`, `T 3 = 23`, `T 4 = 51` obtained by inclusion–exclusion outside Lean
(see `ComputationalEvidence.md`).
-/

open RainbowAP







open RainbowAP in
lemma solution{k m : ℕ} (hk : 2 ≤ k)
    (h : (k ^ 2) ^ m < (k ^ 2 + 1) * (k ^ 2 - 1) ^ m) : m < T k := by
  have hge := card_pair_alphabet_ge k hk
  have hcard := card_pair_alphabet k
  have hne := spectrum_set_nonempty (α := Fin k × Fin k) hge
  have hcrit : Fintype.card (Fin k × Fin k) ^ m < 2 * nonSurjCount (Fin k × Fin k) m := by
    refine majority_nonSurjective_of m hge ?_
    rw [hcard]
    exact h
  by_contra hcon
  push_neg at hcon
  rw [T] at hcon
  have hmaj := (majority_iff_threshold_le hge hne m).2 hcon
  omega
