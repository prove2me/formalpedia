-- Prove2me | Definitions.Def_Shared_AbstractAlgebra_QuatNorm
-- name    : Shared_AbstractAlgebra_QuatNorm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:36.058894+00:00
-- url     : https://prove2.me/theorems/24695f26-d9a1-48a5-b509-2fd3e10232cc
-- title:
--   Aether Catalog definitions — Shared_AbstractAlgebra_QuatNorm
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.AbstractAlgebra.QuatNorm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/AbstractAlgebra/QuatNorm.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.QuatNorm

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

/-- The norm of a quaternion (a, b, c, d) is a² + b² + c² + d². -/
def quatNorm (a b c d : ℤ) : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2


