-- Prove2me | Theorems.Thm_RainbowAP_card_mul_surjSet_le
-- name    : RainbowAP.card_mul_surjSet_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:26:46.211018+00:00
-- url     : https://prove2.me/theorems/96f7898e-90d1-4b5a-bfdb-da2eb09c0093
-- title:
--   Card mul surj set le
-- statement:
--   Formal statement of `RainbowAP.card_mul_surjSet_le` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RainbowAP.card_mul_surjSet_le(m : ℕ) :
--       Fintype.card α * (surjSet α m).card ≤ (surjSet α (m + 1)).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPMonotone.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPMonotone.lean#L48

-- Thm stub generated from Shared/RainbowAPMonotone.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPMonotone
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

theorem RainbowAP.card_mul_surjSet_le(m : ℕ) :
    Fintype.card α * (surjSet α m).card ≤ (surjSet α (m + 1)).card := by sorry
