-- Prove2me | Definitions.Def_Shared_AbstractAlgebra_Spb
-- name    : Shared_AbstractAlgebra_Spb
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:35.329997+00:00
-- url     : https://prove2.me/theorems/7b251a5f-8730-4c0c-a517-cd8c98af8309
-- title:
--   Aether Catalog definitions — Shared_AbstractAlgebra_Spb
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.AbstractAlgebra.Spb`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/AbstractAlgebra/Spb.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Spb

Auto-generated from theorem catalog database.
Domain: Shared
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


