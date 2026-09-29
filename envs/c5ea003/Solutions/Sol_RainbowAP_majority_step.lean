-- Prove2me | solution 1 for RainbowAP.majority_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:35:20.13616+00:00
-- url     : https://prove2.me/submissions/c30d671f-df64-457f-891e-8596dc9ed8b4

-- Sol generated from Shared/RainbowAPMonotone.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPMonotone
import Definitions.Def_Shared_RainbowAPSpectrumThreshold
import Theorems.Thm_RainbowAP_card_mul_surjSet_le
import Theorems.Thm_RainbowAP_card_surjSet_add_nonSurjCount

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









open RainbowAP in
lemma solution{m : ℕ} (hN : 1 ≤ Fintype.card α)
    (h : 2 * nonSurjCount α m < Fintype.card α ^ m) :
    2 * nonSurjCount α (m + 1) < Fintype.card α ^ (m + 1) := by
  have hm := card_surjSet_add_nonSurjCount (α := α) m
  have hm1 := card_surjSet_add_nonSurjCount (α := α) (m + 1)
  have hext := card_mul_surjSet_le (α := α) m
  have hpos : 0 < Fintype.card α := by omega
  have hgrow : Fintype.card α ^ (m + 1) = Fintype.card α * Fintype.card α ^ m := by ring
  have hhalf : Fintype.card α ^ m < 2 * (surjSet α m).card := by omega
  have h1 : Fintype.card α * (Fintype.card α ^ m)
      < Fintype.card α * (2 * (surjSet α m).card) := by
    exact mul_lt_mul_of_pos_left hhalf hpos
  have h2 : Fintype.card α * (2 * (surjSet α m).card)
      = 2 * (Fintype.card α * (surjSet α m).card) := by ring
  omega
