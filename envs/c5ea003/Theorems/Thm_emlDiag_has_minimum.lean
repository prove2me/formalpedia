-- Prove2me | Theorems.Thm_emlDiag_has_minimum
-- name    : emlDiag_has_minimum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:54:19.666023+00:00
-- url     : https://prove2.me/theorems/a983b1d0-e87d-4a5a-9d58-7d9c75684239
-- title:
--   EmlDiag has minimum
-- statement:
--   Formal statement of `emlDiag_has_minimum` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem emlDiag_has_minimum:
--       ∃ z₀ ∈ Ioi (0 : ℝ), ∀ z ∈ Ioi (0 : ℝ), emlDiag z₀ ≤ emlDiag z := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/AbstractAlgebra/EmlDiag.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/AbstractAlgebra/EmlDiag.lean#L31

-- Thm stub generated from Shared/AbstractAlgebra/EmlDiag.lean
import Mathlib
import Definitions.Def_Shared_AbstractAlgebra_EmlDiag

open Set

/-! # CatalogBuild.Shared.EmlDiag

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

noncomputable section

theorem emlDiag_has_minimum:
    ∃ z₀ ∈ Ioi (0 : ℝ), ∀ z ∈ Ioi (0 : ℝ), emlDiag z₀ ≤ emlDiag z := by sorry
