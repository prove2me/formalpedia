-- Prove2me | Definitions.Def_Algebra_AbstractAlgebra_Spb
-- name    : Algebra_AbstractAlgebra_Spb
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:05:17.888099+00:00
-- url     : https://prove2.me/theorems/15b7d09a-b6a2-4d9e-9585-610964823f3d
-- title:
--   Aether Catalog definitions — Algebra_AbstractAlgebra_Spb
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.AbstractAlgebra.Spb`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/AbstractAlgebra/Spb.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Spb

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 25

Repaired: the declarations are now in dependency order and the three objects the
file used without defining (`spb`, `crossRatio`, `spbMat`, together with the
trace/determinant lemmas and the Cauchy pull-back identity) are supplied here.
-/

noncomputable section

open Matrix

/-- [Section: ## Core Definitions] -/
def spb (x y : ℝ) : ℝ := (x + y) / (1 - x * y)

/-- The cross ratio of four points of the real line. -/
def crossRatio (a b c d : ℝ) : ℝ := ((a - c) * (b - d)) / ((a - d) * (b - c))

/-- The SPB matrix `M(a) = [[1, a], [-a, 1]]`, the Möbius representative of
`spb · a`. -/
def spbMat (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, a; -a, 1]




























end


