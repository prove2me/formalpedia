-- Prove2me | Definitions.Def_Applications_AbstractAlgebra_QuatNorm_nonneg
-- name    : Applications_AbstractAlgebra_QuatNorm_nonneg
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:02:27.761683+00:00
-- url     : https://prove2.me/theorems/aeeec446-b165-4b23-86ef-a0209a48614f
-- title:
--   Aether Catalog definitions — Applications_AbstractAlgebra_QuatNorm_nonneg
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AbstractAlgebra.QuatNorm.nonneg`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AbstractAlgebra/QuatNorm_nonneg.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.QuatNorm_nonneg

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 3
-/

/-- The norm of a quaternion (a, b, c, d) is a² + b² + c² + d². -/
def quatNorm (a b c d : ℤ) : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2


