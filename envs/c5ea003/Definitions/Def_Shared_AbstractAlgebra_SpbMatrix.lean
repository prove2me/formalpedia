-- Prove2me | Definitions.Def_Shared_AbstractAlgebra_SpbMatrix
-- name    : Shared_AbstractAlgebra_SpbMatrix
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:00.207904+00:00
-- url     : https://prove2.me/theorems/597c7099-6f03-486f-b99e-2ae4e30d74f3
-- title:
--   Aether Catalog definitions — Shared_AbstractAlgebra_SpbMatrix
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.AbstractAlgebra.SpbMatrix`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/AbstractAlgebra/SpbMatrix.lean by skeleton subtraction
import Mathlib

open Matrix

/-! # CatalogBuild.Shared.SpbMatrix

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 8
-/

noncomputable section

/-- The SPB matrix: M(a) = [[1, a], [-a, 1]]. -/
def spbMatrix (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, a; -a, 1]








end


