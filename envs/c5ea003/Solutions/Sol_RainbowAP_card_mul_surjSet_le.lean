-- Prove2me | solution 1 for RainbowAP.card_mul_surjSet_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:34:00.573099+00:00
-- url     : https://prove2.me/submissions/e75d7042-35a5-488e-a26b-a0b39eecc15e

-- Sol generated from Shared/RainbowAPMonotone.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPMonotone
import Definitions.Def_Shared_RainbowAPSpectrumMoments
import Definitions.Def_Shared_RainbowAPSpectrumThreshold
import Theorems.Thm_RainbowAP_missCount_eq_zero_iff

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


lemma mem_surjSet {m : ℕ} (f : Fin m → α) :
    f ∈ surjSet α m ↔ Function.Surjective f := by
  simp [surjSet, missCount_eq_zero_iff]







open RainbowAP in
lemma solution(m : ℕ) :
    Fintype.card α * (surjSet α m).card ≤ (surjSet α (m + 1)).card := by
  have hmap : ∀ p ∈ (univ : Finset α) ×ˢ surjSet α m,
      (fun p : α × (Fin m → α) => (Fin.snoc p.2 p.1 : Fin (m + 1) → α)) p
        ∈ surjSet α (m + 1) := by
    rintro ⟨a, f⟩ hp
    simp only [Finset.mem_product, Finset.mem_univ, true_and] at hp
    rw [mem_surjSet] at hp ⊢
    intro b
    obtain ⟨i, hi⟩ := hp b
    exact ⟨i.castSucc, by simpa [Fin.snoc_castSucc] using hi⟩
  have hinj : Set.InjOn (fun p : α × (Fin m → α) => (Fin.snoc p.2 p.1 : Fin (m + 1) → α))
      ((univ : Finset α) ×ˢ surjSet α m) := by
    rintro ⟨a, f⟩ _ ⟨b, g⟩ _ hfg
    simp only at hfg
    have hlast : a = b := by
      have := congrArg (fun w => w (Fin.last m)) hfg
      simpa [Fin.snoc_last] using this
    have hrest : f = g := by
      funext i
      have := congrArg (fun w => w i.castSucc) hfg
      simpa [Fin.snoc_castSucc] using this
    simp [hlast, hrest]
  have hinj' : Set.InjOn (fun p : α × (Fin m → α) => (Fin.snoc p.2 p.1 : Fin (m + 1) → α))
      ((univ ×ˢ surjSet α m : Finset (α × (Fin m → α)))) := by
    intro x hx y hy hxy
    exact hinj (by simpa using hx) (by simpa using hy) hxy
  have hcard := Finset.card_le_card_of_injOn _ hmap hinj'
  simpa [Finset.card_product, Finset.card_univ] using hcard
