-- Prove2me | Definitions.Def_Algebra_EtowerStrictmono_ETower_strictMono
-- name    : Algebra_EtowerStrictmono_ETower_strictMono
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:14:10.729074+00:00
-- url     : https://prove2.me/theorems/b7fbf002-e7d4-4eb2-aa61-aa3486a23a5b
-- title:
--   Aether Catalog definitions — Algebra_EtowerStrictmono_ETower_strictMono
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.EtowerStrictmono.ETower.strictMono`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/EtowerStrictmono/ETower_strictMono.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.ETower_strictMono

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 5

Repaired: `eTower` moved before its uses, the two stray `end`s removed, and the
`exact?` placeholder inside `eTower_ge_pow2` replaced by a genuine proof (via
the elementary bound `2x ≤ exp x`).
-/

noncomputable section

/-- The e-tower: e↑↑n. -/
def eTower : ℕ → ℝ
  | 0 => 1
  | n + 1 => Real.exp (eTower n)






end


