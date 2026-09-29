-- Prove2me | Definitions.Def_NumberTheory_EtowerStrictmono_ETower_strictMono
-- name    : NumberTheory_EtowerStrictmono_ETower_strictMono
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:07:10.069866+00:00
-- url     : https://prove2.me/theorems/5718af2c-5cda-4996-8f18-f4e2f16766e6
-- title:
--   Aether Catalog definitions — NumberTheory_EtowerStrictmono_ETower_strictMono
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.EtowerStrictmono.ETower.strictMono`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/EtowerStrictmono/ETower_strictMono.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.ETower_strictMono

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 5
-/

noncomputable section

/-- The e-tower: e↑↑n. -/
def eTower : ℕ → ℝ
  | 0 => 1
  | n + 1 => Real.exp (eTower n)





end


