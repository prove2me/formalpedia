-- Prove2me | Theorems.Thm_RainbowAP_majority_step
-- name    : RainbowAP.majority_step
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:26:57.743875+00:00
-- url     : https://prove2.me/theorems/595ccb06-ede7-40af-86f7-7912b69646b6
-- title:
--   Majority step
-- statement:
--   Formal statement of `RainbowAP.majority_step` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RainbowAP.majority_step{m : ℕ} (hN : 1 ≤ Fintype.card α)
--       (h : 2 * nonSurjCount α m < Fintype.card α ^ m) :
--       2 * nonSurjCount α (m + 1) < Fintype.card α ^ (m + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPMonotone.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPMonotone.lean#L80

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

theorem RainbowAP.majority_step{m : ℕ} (hN : 1 ≤ Fintype.card α)
    (h : 2 * nonSurjCount α m < Fintype.card α ^ m) :
    2 * nonSurjCount α (m + 1) < Fintype.card α ^ (m + 1) := by sorry
