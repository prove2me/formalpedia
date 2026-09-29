-- Prove2me | solution 1 for RainbowAP.majority_iff_threshold_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:36:41.031834+00:00
-- url     : https://prove2.me/submissions/074f5b24-6f91-4946-913a-e9b903f90a24

-- Sol generated from Shared/RainbowAPMonotone.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPMonotone
import Definitions.Def_Shared_RainbowAPSpectrumThreshold
import Theorems.Thm_RainbowAP_majority_step
import Theorems.Thm_RainbowAP_mem_of_spectrumThreshold
import Theorems.Thm_RainbowAP_spectrumThreshold_le_of_mem

/-!
# The full-spectrum transition is monotone: `spectrumThreshold` is a genuine threshold

The definition of `spectrumThreshold α` as an infimum only says that *some* length realises a
surjective majority.  Here we prove that the majority property is upward closed in the word
length, so that

  `2 * nonSurjCount α m < |α| ^ m  ↔  spectrumThreshold α ≤ m`,

i.e. the transition happens exactly once.  The combinatorial engine is the extension injection
`(a, f) ↦ Fin.snoc f a`, which shows `|α| · Surj(m) ≤ Surj(m+1)`.
-/

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]






/-- The surjective majority property is upward closed in the word length. -/
theorem majority_monotone (hN : 1 ≤ Fintype.card α) {m m' : ℕ} (hmm : m ≤ m')
    (h : 2 * nonSurjCount α m < Fintype.card α ^ m) :
    2 * nonSurjCount α m' < Fintype.card α ^ m' := by
  induction m' with
  | zero => simpa [Nat.le_zero.1 hmm] using h
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact majority_step hN (ih (by omega))
      · have : m = n + 1 := by omega
        simpa [this] using h



open RainbowAP in
theorem solution(hN : 2 ≤ Fintype.card α)
    (hne : {m | 2 * nonSurjCount α m < Fintype.card α ^ m}.Nonempty) (m : ℕ) :
    (2 * nonSurjCount α m < Fintype.card α ^ m) ↔ spectrumThreshold α ≤ m := by
  constructor
  · intro h
    exact spectrumThreshold_le_of_mem h
  · intro h
    exact majority_monotone (by omega) h (mem_of_spectrumThreshold hne)
