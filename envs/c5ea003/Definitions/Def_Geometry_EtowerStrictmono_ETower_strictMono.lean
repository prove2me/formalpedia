-- Prove2me | Definitions.Def_Geometry_EtowerStrictmono_ETower_strictMono
-- name    : Geometry_EtowerStrictmono_ETower_strictMono
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:12:54.05314+00:00
-- url     : https://prove2.me/theorems/9aafa231-4eea-4b52-bf99-4725138fbed8
-- title:
--   Aether Catalog definitions — Geometry_EtowerStrictmono_ETower_strictMono
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.EtowerStrictmono.ETower.strictMono`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/EtowerStrictmono/ETower_strictMono.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.ETower_strictMono

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 5

Repaired: the definition `eTower` now precedes the statements about it, the
stray `end` markers are removed, and the two proofs that were left open
(`eTower_strictMono`, `eTower_ge_pow2`) are completed.  The growth step
`2 * x ≤ exp x` is isolated as `two_mul_le_exp`, proved by squaring the
elementary bound `1 + x/2 ≤ exp (x/2)`.
-/

noncomputable section

/-- The e-tower: e↑↑n. -/
def eTower : ℕ → ℝ
  | 0 => 1
  | n + 1 => Real.exp (eTower n)






end


