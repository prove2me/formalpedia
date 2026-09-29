-- Prove2me | Theorems.Thm_eTower_ge_pow2
-- name    : eTower_ge_pow2
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:54:13.102565+00:00
-- url     : https://prove2.me/theorems/88470784-1bf0-479e-af33-88c22dbe9b03
-- title:
--   [Section: # CatalogBuild.Shared.ETower_strictMono
-- statement:
--   [Section: # CatalogBuild.Shared.ETower_strictMono
--   Auto-generated from theorem catalog database.
--   Domain: Shared
--   Declarations: 5]
--
--   ```lean
--   theorem eTower_ge_pow2(n : ℕ) (hn : 1 ≤ n) : eTower n ≥ 2 ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/EtowerStrictmono/ETower_strictMono.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/EtowerStrictmono/ETower_strictMono.lean#L50

-- Thm stub generated from Shared/EtowerStrictmono/ETower_strictMono.lean
import Mathlib
import Definitions.Def_Shared_EtowerStrictmono_ETower_strictMono

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

theorem eTower_ge_pow2(n : ℕ) (hn : 1 ≤ n) : eTower n ≥ 2 ^ n := by sorry
