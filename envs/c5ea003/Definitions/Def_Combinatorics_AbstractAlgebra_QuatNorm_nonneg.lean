-- Prove2me | Definitions.Def_Combinatorics_AbstractAlgebra_QuatNorm_nonneg
-- name    : Combinatorics_AbstractAlgebra_QuatNorm_nonneg
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:28:25.240955+00:00
-- url     : https://prove2.me/theorems/0e422822-63a0-4c1d-808e-ce8e121d65fb
-- title:
--   Aether Catalog definitions — Combinatorics_AbstractAlgebra_QuatNorm_nonneg
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.AbstractAlgebra.QuatNorm.nonneg`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/AbstractAlgebra/QuatNorm_nonneg.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.QuatNorm_nonneg

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 3
-/


/-- The norm of a quaternion (a, b, c, d) is a² + b² + c² + d². -/
def quatNorm (a b c d : ℤ) : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2


