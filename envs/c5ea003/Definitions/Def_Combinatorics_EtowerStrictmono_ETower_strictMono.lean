-- Prove2me | Definitions.Def_Combinatorics_EtowerStrictmono_ETower_strictMono
-- name    : Combinatorics_EtowerStrictmono_ETower_strictMono
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:43:20.736913+00:00
-- url     : https://prove2.me/theorems/c7b1e217-05ca-4fcd-97be-2ba5eed51cdd
-- title:
--   Aether Catalog definitions — Combinatorics_EtowerStrictmono_ETower_strictMono
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.EtowerStrictmono.ETower.strictMono`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/EtowerStrictmono/ETower_strictMono.lean by skeleton subtraction
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


