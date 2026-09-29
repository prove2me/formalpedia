-- Prove2me | solution 1 for RainbowAP.mem_missing
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:31:12.993349+00:00
-- url     : https://prove2.me/submissions/77c7ffe6-5158-4320-ac69-0de0ca80782a

-- Sol generated from Shared/RainbowAPSpectrumMoments.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]











open RainbowAP in
lemma solution{m : ℕ} (f : Fin m → α) (a : α) :
    a ∈ missing f ↔ ∀ x, f x ≠ a := by
  simp [missing]
