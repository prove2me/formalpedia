-- Prove2me | Definitions.Def_Tropical_AbstractAlgebra_Spb_comm
-- name    : Tropical_AbstractAlgebra_Spb_comm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:04.131603+00:00
-- url     : https://prove2.me/theorems/19782b5d-f49c-4ec5-a842-078d518fe02f
-- title:
--   Aether Catalog definitions — Tropical_AbstractAlgebra_Spb_comm
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.AbstractAlgebra.Spb.comm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/AbstractAlgebra/Spb_comm.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Spb_comm

Auto-generated from theorem catalog database.
Domain: EML
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


