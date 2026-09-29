-- Prove2me | Definitions.Def_Shared_AbstractAlgebra_SpbMatrix_det_mul
-- name    : Shared_AbstractAlgebra_SpbMatrix_det_mul
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:47:39.039324+00:00
-- url     : https://prove2.me/theorems/67d8e8d4-5837-43ad-801b-4396e60f4d21
-- title:
--   Aether Catalog definitions — Shared_AbstractAlgebra_SpbMatrix_det_mul
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.AbstractAlgebra.SpbMatrix.det.mul`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/AbstractAlgebra/SpbMatrix_det_mul.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.SpbMatrix_det_mul

Auto-generated from theorem catalog database.
Domain: EML
Declarations: 8
-/


open Matrix

noncomputable section

/-- The SPB matrix: M(a) = [[1, a], [-a, 1]]. -/
def spbMatrix (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, a; -a, 1]








end


