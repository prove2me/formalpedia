-- Prove2me | Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple
-- name    : Shared_Ispythquadruple_IsPythQuadruple
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:54:12.010925+00:00
-- url     : https://prove2.me/theorems/6613cd42-cb84-4020-9f75-693428ade070
-- title:
--   Aether Catalog definitions — Shared_Ispythquadruple_IsPythQuadruple
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.Ispythquadruple.IsPythQuadruple`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/Ispythquadruple/IsPythQuadruple.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.IsPythQuadruple

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1
-/

/-- A Pythagorean quadruple (a, b, c, d) satisfies a² + b² + c² = d² -/
def IsPythQuadruple (a b c d : ℤ) : Prop :=
  a^2 + b^2 + c^2 = d^2


