-- Prove2me | Definitions.Def_Shared_AbstractAlgebra_QuatNorm_nonneg
-- name    : Shared_AbstractAlgebra_QuatNorm_nonneg
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:47:59.543692+00:00
-- url     : https://prove2.me/theorems/8db1f8e5-b49f-4acc-a4e3-d69e8051452b
-- title:
--   Aether Catalog definitions — Shared_AbstractAlgebra_QuatNorm_nonneg
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.AbstractAlgebra.QuatNorm.nonneg`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/AbstractAlgebra/QuatNorm_nonneg.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.QuatNorm_nonneg

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 3
-/


/-- The norm of a quaternion (a, b, c, d) is a² + b² + c² + d². -/
def quatNorm (a b c d : ℤ) : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2


