-- Prove2me | Definitions.Def_Speculative_Shared_QuatNorm
-- name    : Speculative_Shared_QuatNorm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:54.72277+00:00
-- url     : https://prove2.me/theorems/6ab731de-01f5-47a3-85ef-2eb705f441f8
-- title:
--   Aether Catalog definitions — Speculative_Shared_QuatNorm
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.Shared.QuatNorm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/Shared/QuatNorm.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.QuatNorm

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

/-- The norm of a quaternion (a, b, c, d) is a² + b² + c² + d². -/
def quatNorm (a b c d : ℤ) : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2


