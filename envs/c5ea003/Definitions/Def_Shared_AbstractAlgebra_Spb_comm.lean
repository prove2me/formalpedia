-- Prove2me | Definitions.Def_Shared_AbstractAlgebra_Spb_comm
-- name    : Shared_AbstractAlgebra_Spb_comm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:48:28.817686+00:00
-- url     : https://prove2.me/theorems/0b8aab10-8463-4521-86ea-b128e2848e60
-- title:
--   Aether Catalog definitions — Shared_AbstractAlgebra_Spb_comm
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.AbstractAlgebra.Spb.comm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/AbstractAlgebra/Spb_comm.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Spb_comm

Auto-generated from theorem catalog database.
Domain: EML
Declarations: 25
-/


noncomputable section

/-- The cross ratio of four reals. -/
def crossRatio (a b c d : ℝ) : ℝ := ((a - c) * (b - d)) / ((a - d) * (b - c))

/-- The SPB matrix `M(a) = !![1, a; -a, 1]`. -/
def spbMat (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, a; -a, 1]





/-- [Section: ## Core Definitions] -/
def spb (x y : ℝ) : ℝ := (x + y) / (1 - x * y)
























end


