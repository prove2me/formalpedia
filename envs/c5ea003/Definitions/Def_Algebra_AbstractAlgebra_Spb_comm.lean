-- Prove2me | Definitions.Def_Algebra_AbstractAlgebra_Spb_comm
-- name    : Algebra_AbstractAlgebra_Spb_comm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:05:24.218071+00:00
-- url     : https://prove2.me/theorems/b746987d-f437-42bb-806d-011d6e1aa241
-- title:
--   Aether Catalog definitions — Algebra_AbstractAlgebra_Spb_comm
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.AbstractAlgebra.Spb.comm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/AbstractAlgebra/Spb_comm.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Spb_comm

Auto-generated from theorem catalog database.
Domain: EML
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


