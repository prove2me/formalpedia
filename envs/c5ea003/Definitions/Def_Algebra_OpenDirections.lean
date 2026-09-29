-- Prove2me | Definitions.Def_Algebra_OpenDirections
-- name    : Algebra_OpenDirections
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:26:17.344168+00:00
-- url     : https://prove2.me/theorems/809035bd-e5ce-4d42-b713-93e1f744f2d7
-- title:
--   Aether Catalog definitions — Algebra_OpenDirections
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.OpenDirections`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/OpenDirections.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.OpenDirections

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 42
-/























/-- Lens reduction: S → S/b. -/
def lensReduce (S b : ℕ) : ℕ := S / b















/-- An abstract lens: a monotone function on search spaces. -/
structure AbstractLens where
  reduce : ℕ → ℕ
  monotone : ∀ S, reduce S ≤ S


/-- A halving lens: S ↦ S/2. -/
def halvingLens : AbstractLens where
  reduce := fun S => S / 2
  monotone := fun S => Nat.div_le_self S 2


