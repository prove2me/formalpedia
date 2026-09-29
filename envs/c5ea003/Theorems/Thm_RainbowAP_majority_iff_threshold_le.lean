-- Prove2me | Theorems.Thm_RainbowAP_majority_iff_threshold_le
-- name    : RainbowAP.majority_iff_threshold_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:49:29.400497+00:00
-- url     : https://prove2.me/theorems/84bb04fa-095d-4cfd-88d1-783266936692
-- title:
--   The threshold is a genuine phase transition.
-- statement:
--   **The threshold is a genuine phase transition.**
--
--   ```lean
--   theorem RainbowAP.majority_iff_threshold_le(hN : 2 ≤ Fintype.card α)
--       (hne : {m | 2 * nonSurjCount α m < Fintype.card α ^ m}.Nonempty) (m : ℕ) :
--       (2 * nonSurjCount α m < Fintype.card α ^ m) ↔ spectrumThreshold α ≤ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPMonotone.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPMonotone.lean#L108

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

theorem RainbowAP.majority_iff_threshold_le(hN : 2 ≤ Fintype.card α)
    (hne : {m | 2 * nonSurjCount α m < Fintype.card α ^ m}.Nonempty) (m : ℕ) :
    (2 * nonSurjCount α m < Fintype.card α ^ m) ↔ spectrumThreshold α ≤ m := by sorry
