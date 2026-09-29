-- Prove2me | Theorems.Thm_RainbowAP_card_avoid_two
-- name    : RainbowAP.card_avoid_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:25:57.742056+00:00
-- url     : https://prove2.me/theorems/26981333-9868-41de-a422-191b322982d7
-- title:
--   Card avoid two
-- statement:
--   Formal statement of `RainbowAP.card_avoid_two` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RainbowAP.card_avoid_two(m : ℕ) (a b : α) (hab : a ≠ b) :
--       (univ.filter (fun f : Fin m → α => (∀ x, f x ≠ a) ∧ (∀ x, f x ≠ b))).card
--         = (Fintype.card α - 2) ^ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/RainbowAPSpectrumMoments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/RainbowAPSpectrumMoments.lean#L48

-- Thm stub generated from Shared/RainbowAPSpectrumMoments.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem RainbowAP.card_avoid_two(m : ℕ) (a b : α) (hab : a ≠ b) :
    (univ.filter (fun f : Fin m → α => (∀ x, f x ≠ a) ∧ (∀ x, f x ≠ b))).card
      = (Fintype.card α - 2) ^ m := by sorry
