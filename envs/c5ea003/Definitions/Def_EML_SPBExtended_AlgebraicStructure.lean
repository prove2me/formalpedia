-- Prove2me | Definitions.Def_EML_SPBExtended_AlgebraicStructure
-- name    : EML_SPBExtended_AlgebraicStructure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:45.795706+00:00
-- url     : https://prove2.me/theorems/ecf381c8-0978-4d0a-9536-da6f57c127fa
-- title:
--   Aether Catalog definitions — EML_SPBExtended_AlgebraicStructure
-- statement:
--   Definition bundle for the Aether Catalog module `EML.SPBExtended.AlgebraicStructure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/SPBExtended/AlgebraicStructure.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Computation.AlgebraicStructure

Auto-generated from theorem catalog database.
Domain: Computation
Declarations: 21
-/


noncomputable section

/-- The EML operation. -/
def EMLa (a b : ℝ) : ℝ := Real.exp a - Real.log b
































/-- T_c(x) = EML(x, c) = exp(x) - ln(c). -/
def Tc (c : ℝ) (x : ℝ) : ℝ := EMLa x c




































/-- n-fold EML tower: EML(EML(...EML(1,1)..., 1), 1) = exp^n(1) = e↑↑n. -/
def EMLTower : ℕ → ℝ
  | 0 => 1
  | n + 1 => EMLa (EMLTower n) 1
















end


