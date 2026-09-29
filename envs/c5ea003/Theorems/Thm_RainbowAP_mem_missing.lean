-- Prove2me | Theorems.Thm_RainbowAP_mem_missing
-- name    : RainbowAP.mem_missing
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:26:29.001358+00:00
-- url     : https://prove2.me/theorems/4cac8f59-237c-4468-a18a-0b1f5bd9370e
-- title:
--   Mem missing
-- statement:
--   Formal statement of `RainbowAP.mem_missing` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RainbowAP.mem_missing{m : ℕ} (f : Fin m → α) (a : α) :
--       a ∈ missing f ↔ ∀ x, f x ≠ a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumMoments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumMoments.lean#L16

-- Thm stub generated from Shared/RainbowAPSpectrumMoments.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem RainbowAP.mem_missing{m : ℕ} (f : Fin m → α) (a : α) :
    a ∈ missing f ↔ ∀ x, f x ≠ a := by sorry
