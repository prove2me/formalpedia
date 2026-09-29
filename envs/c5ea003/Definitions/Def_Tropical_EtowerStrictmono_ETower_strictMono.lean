-- Prove2me | Definitions.Def_Tropical_EtowerStrictmono_ETower_strictMono
-- name    : Tropical_EtowerStrictmono_ETower_strictMono
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:30:08.974472+00:00
-- url     : https://prove2.me/theorems/83b2e4bd-13cf-45ff-883e-383c095ff6b4
-- title:
--   Aether Catalog definitions — Tropical_EtowerStrictmono_ETower_strictMono
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.EtowerStrictmono.ETower.strictMono`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/EtowerStrictmono/ETower_strictMono.lean by skeleton subtraction
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


