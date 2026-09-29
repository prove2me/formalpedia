-- Prove2me | Theorems.Thm_RainbowAP_sum_missCount
-- name    : RainbowAP.sum_missCount
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:25:49.465037+00:00
-- url     : https://prove2.me/theorems/e8836c04-14ee-483d-9516-d805036b7ce5
-- title:
--   Sum miss count
-- statement:
--   Formal statement of `RainbowAP.sum_missCount` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RainbowAP.sum_missCount(m : ℕ) :
--       ∑ f : Fin m → α, missCount f = Fintype.card α * (Fintype.card α - 1) ^ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumMoments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumMoments.lean#L69

-- Thm stub generated from Shared/RainbowAPSpectrumMoments.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem RainbowAP.sum_missCount(m : ℕ) :
    ∑ f : Fin m → α, missCount f = Fintype.card α * (Fintype.card α - 1) ^ m := by sorry
