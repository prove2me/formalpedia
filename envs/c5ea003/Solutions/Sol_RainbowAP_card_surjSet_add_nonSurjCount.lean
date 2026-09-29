-- Prove2me | solution 1 for RainbowAP.card_surjSet_add_nonSurjCount
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:34:01.33014+00:00
-- url     : https://prove2.me/submissions/71e9373a-695c-4736-9483-c21750295946

-- Sol generated from Shared/RainbowAPMonotone.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPMonotone
import Definitions.Def_Shared_RainbowAPSpectrumMoments
import Definitions.Def_Shared_RainbowAPSpectrumThreshold

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
lemma solution(m : ℕ) :
    (surjSet α m).card + nonSurjCount α m = Fintype.card α ^ m := by
  have hpart := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin m → α))) (p := fun f => missCount f = 0)
  have hneg : (univ : Finset (Fin m → α)).filter (fun f => ¬ (missCount f = 0))
      = nonSurjSet α m := by
    unfold nonSurjSet
    apply Finset.filter_congr
    intro f _
    simp [Nat.pos_iff_ne_zero]
  rw [hneg] at hpart
  have hcard : (univ : Finset (Fin m → α)).card = Fintype.card α ^ m := by
    simp [Finset.card_univ]
  rw [hcard] at hpart
  exact hpart
