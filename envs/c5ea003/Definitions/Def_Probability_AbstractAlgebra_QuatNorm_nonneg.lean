-- Prove2me | Definitions.Def_Probability_AbstractAlgebra_QuatNorm_nonneg
-- name    : Probability_AbstractAlgebra_QuatNorm_nonneg
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:26.758411+00:00
-- url     : https://prove2.me/theorems/ca377c4d-f29b-4c36-8619-161cb71b19fa
-- title:
--   Aether Catalog definitions — Probability_AbstractAlgebra_QuatNorm_nonneg
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.AbstractAlgebra.QuatNorm.nonneg`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/AbstractAlgebra/QuatNorm_nonneg.lean by skeleton subtraction
import Mathlib
/-! # CatalogBuild.Shared.QuatNorm_nonneg

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 3
-/

/-- The norm of a quaternion (a, b, c, d) is a² + b² + c² + d². -/
def quatNorm (a b c d : ℤ) : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2


