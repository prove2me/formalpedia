-- Prove2me | Definitions.Def_Tropical_AbstractAlgebra_Spb
-- name    : Tropical_AbstractAlgebra_Spb
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:28:59.864328+00:00
-- url     : https://prove2.me/theorems/85e9fa4f-2900-4956-af91-a0d2999725df
-- title:
--   Aether Catalog definitions — Tropical_AbstractAlgebra_Spb
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.AbstractAlgebra.Spb`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/AbstractAlgebra/Spb.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Spb

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 25
-/

open Matrix

noncomputable section

/-- The SPB matrix `M(a) = [[1, a], [-a, 1]]`. -/
def spbMat (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, a; -a, 1]



/-- The cross ratio of four points of the real projective line. -/
def crossRatio (a b c d : ℝ) : ℝ := ((a - c) * (b - d)) / ((a - d) * (b - c))


/-- [Section: ## Core Definitions] -/
def spb (x y : ℝ) : ℝ := (x + y) / (1 - x * y)


























end


