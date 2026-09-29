-- Prove2me | Definitions.Def_Shared_RainbowAPMonotone
-- name    : Shared_RainbowAPMonotone
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:13:04.645622+00:00
-- url     : https://prove2.me/theorems/cf98e2ec-e691-43a3-9b43-8f13290fcbad
-- title:
--   Aether Catalog definitions — Shared_RainbowAPMonotone
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.RainbowAPMonotone`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/RainbowAPMonotone.lean by skeleton subtraction
import Mathlib
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

namespace RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The surjective (full-spectrum) words of length `m`. -/
def surjSet (α : Type*) [Fintype α] [DecidableEq α] (m : ℕ) : Finset (Fin m → α) :=
  (univ : Finset (Fin m → α)).filter (fun f => missCount f = 0)







end RainbowAP


