-- Prove2me | solution 1 for RainbowAP.missCount_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:32:47.483794+00:00
-- url     : https://prove2.me/submissions/c4bbe430-ddf9-40a5-b2e9-25adf2d147cd

-- Sol generated from Shared/RainbowAPSpectrumMoments.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments
import Theorems.Thm_RainbowAP_mem_missing

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]











open RainbowAP in
lemma solution{m : ℕ} (f : Fin m → α) :
    missCount f = 0 ↔ Function.Surjective f := by
  constructor
  · intro h a
    by_contra hc
    push_neg at hc
    have hmem : a ∈ missing f := (mem_missing f a).2 (fun x hx => hc x hx)
    rw [missCount, Finset.card_eq_zero] at h
    rw [h] at hmem
    simp at hmem
  · intro h
    rw [missCount, Finset.card_eq_zero]
    ext a
    simp only [mem_missing, Finset.notMem_empty, iff_false, not_forall, not_not]
    obtain ⟨x, hx⟩ := h a
    exact ⟨x, hx⟩
