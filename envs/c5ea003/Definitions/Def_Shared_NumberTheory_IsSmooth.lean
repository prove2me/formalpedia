-- Prove2me | Definitions.Def_Shared_NumberTheory_IsSmooth
-- name    : Shared_NumberTheory_IsSmooth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:04:59.495176+00:00
-- url     : https://prove2.me/theorems/c5b2ed98-625b-4173-b86e-2dcafb20aca4
-- title:
--   Aether Catalog definitions — Shared_NumberTheory_IsSmooth
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.NumberTheory.IsSmooth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/NumberTheory/IsSmooth.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.IsSmooth

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1
-/

/-- [Section: # CatalogBuild.Shared.IsSmooth
Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 1] -/
def isSmooth (B n : ℕ) : Prop := ∀ p, Nat.Prime p → p ∣ n → p ≤ B


