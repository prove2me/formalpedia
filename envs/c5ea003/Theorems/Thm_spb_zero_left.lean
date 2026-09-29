-- Prove2me | Theorems.Thm_spb_zero_left
-- name    : spb_zero_left
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:55:04.059988+00:00
-- url     : https://prove2.me/theorems/1533d251-2ba8-4331-b9e7-4ad546bf45a5
-- title:
--   Zero is a left identity for SPB.
-- statement:
--   Zero is a left identity for SPB.
--
--   ```lean
--   theorem spb_zero_left(x : ℝ) : spb 0 x = x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/AbstractAlgebra/Spb.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/AbstractAlgebra/Spb.lean#L82

-- Thm stub generated from Shared/AbstractAlgebra/Spb_zero_right.lean
import Mathlib
import Definitions.Def_Shared_AbstractAlgebra_Spb_zero_right

open Real

/-! # CatalogBuild.Shared.Spb_zero_right

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 14
-/


noncomputable section

theorem spb_zero_left(x : ℝ) : spb 0 x = x := by sorry
