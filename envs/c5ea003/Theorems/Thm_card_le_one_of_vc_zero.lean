-- Prove2me | Theorems.Thm_card_le_one_of_vc_zero
-- name    : card_le_one_of_vc_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:02:30.883499+00:00
-- url     : https://prove2.me/theorems/5ad2b8ed-4fea-43cf-a23d-fbba4d31ade0
-- title:
--   Card le one of vc zero
-- statement:
--   Formal statement of `card_le_one_of_vc_zero` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem card_le_one_of_vc_zero{n : ℕ} (F : Finset (Finset (Fin n)))
--       (hF : ∀ A, Shatters F A → A.card ≤ 0) : F.card ≤ 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/SauerShelah.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/SauerShelah.lean#L205

-- Thm stub generated from Algebra/SauerShelah.lean
import Mathlib
import Definitions.Def_Algebra_SauerShelah

open Fin

/-! # CatalogBuild.Algebra.SauerShelah

Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 17
-/











-- ================================================================
--  Basic proj / embed API
-- ================================================================

theorem card_le_one_of_vc_zero{n : ℕ} (F : Finset (Finset (Fin n)))
    (hF : ∀ A, Shatters F A → A.card ≤ 0) : F.card ≤ 1 := by sorry
