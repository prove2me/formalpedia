-- Prove2me | Definitions.Def_Speculative_NumberTheory_WallSunSun
-- name    : Speculative_NumberTheory_WallSunSun
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:23.407816+00:00
-- url     : https://prove2.me/theorems/257f5d9d-306f-4d9c-92b1-9c0f33d8ca69
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_WallSunSun
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.WallSunSun`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/WallSunSun.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.WallSunSun

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 13
-/

/-- [Section: # CatalogBuild.Speculative.WallSunSun
Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 13] -/
def IsWieferichPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ 2 ^ (p - 1) % (p ^ 2) = 1


