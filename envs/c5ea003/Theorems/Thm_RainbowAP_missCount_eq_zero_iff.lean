-- Prove2me | Theorems.Thm_RainbowAP_missCount_eq_zero_iff
-- name    : RainbowAP.missCount_eq_zero_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:26:25.365479+00:00
-- url     : https://prove2.me/theorems/937cc94d-fced-4da2-a9a6-ea983474bfb4
-- title:
--   Miss count eq zero iff
-- statement:
--   Formal statement of `RainbowAP.missCount_eq_zero_iff` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RainbowAP.missCount_eq_zero_iff{m : ℕ} (f : Fin m → α) :
--       missCount f = 0 ↔ Function.Surjective f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumMoments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumMoments.lean#L20

-- Thm stub generated from Shared/RainbowAPSpectrumMoments.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem RainbowAP.missCount_eq_zero_iff{m : ℕ} (f : Fin m → α) :
    missCount f = 0 ↔ Function.Surjective f := by sorry
