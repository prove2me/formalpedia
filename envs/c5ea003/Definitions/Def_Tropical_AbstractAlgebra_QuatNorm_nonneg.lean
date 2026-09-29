-- Prove2me | Definitions.Def_Tropical_AbstractAlgebra_QuatNorm_nonneg
-- name    : Tropical_AbstractAlgebra_QuatNorm_nonneg
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:28:48.704257+00:00
-- url     : https://prove2.me/theorems/3e1ebfa7-4cff-4331-a401-51d0e71050a3
-- title:
--   Aether Catalog definitions — Tropical_AbstractAlgebra_QuatNorm_nonneg
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.AbstractAlgebra.QuatNorm.nonneg`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/AbstractAlgebra/QuatNorm_nonneg.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.QuatNorm_nonneg

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 3
-/

/-- The norm of a quaternion (a, b, c, d) is a² + b² + c² + d². -/
def quatNorm (a b c d : ℤ) : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2


