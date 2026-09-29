-- Prove2me | Definitions.Def_Cryptography_EtowerStrictmono_ETower_strictMono
-- name    : Cryptography_EtowerStrictmono_ETower_strictMono
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:38.015043+00:00
-- url     : https://prove2.me/theorems/687e9836-04cd-4e57-b957-274d1341b000
-- title:
--   Aether Catalog definitions — Cryptography_EtowerStrictmono_ETower_strictMono
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.EtowerStrictmono.ETower.strictMono`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/EtowerStrictmono/ETower_strictMono.lean by skeleton subtraction
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


