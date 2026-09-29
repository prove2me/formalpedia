-- Prove2me | Definitions.Def_Algebra_AbstractAlgebra_QuatNorm_nonneg
-- name    : Algebra_AbstractAlgebra_QuatNorm_nonneg
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:05:19.335583+00:00
-- url     : https://prove2.me/theorems/0dee2f9d-8322-425f-8eb5-a2321c0e0798
-- title:
--   Aether Catalog definitions — Algebra_AbstractAlgebra_QuatNorm_nonneg
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.AbstractAlgebra.QuatNorm.nonneg`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/AbstractAlgebra/QuatNorm_nonneg.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.QuatNorm_nonneg

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 3

Repaired: `import` moved to the top of the file and the definition `quatNorm`
placed before the theorems that use it.
-/

noncomputable section

/-- The norm of a quaternion (a, b, c, d) is a² + b² + c² + d². -/
def quatNorm (a b c d : ℤ) : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2



end


