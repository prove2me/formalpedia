-- Prove2me | Theorems.Thm_RainbowAP_sum_missCount_sq
-- name    : RainbowAP.sum_missCount_sq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:26:11.635755+00:00
-- url     : https://prove2.me/theorems/ceeb71cf-8450-41e3-9627-dfff539acb32
-- title:
--   Sum miss count sq
-- statement:
--   Formal statement of `RainbowAP.sum_missCount_sq` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RainbowAP.sum_missCount_sq(m : ℕ) :
--       ∑ f : Fin m → α, (missCount f) ^ 2
--         = Fintype.card α * (Fintype.card α - 1) ^ m
--           + Fintype.card α * (Fintype.card α - 1) * (Fintype.card α - 2) ^ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumMoments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumMoments.lean#L81

-- Thm stub generated from Shared/RainbowAPSpectrumMoments.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem RainbowAP.sum_missCount_sq(m : ℕ) :
    ∑ f : Fin m → α, (missCount f) ^ 2
      = Fintype.card α * (Fintype.card α - 1) ^ m
        + Fintype.card α * (Fintype.card α - 1) * (Fintype.card α - 2) ^ m := by sorry
