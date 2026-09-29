-- Prove2me | Definitions.Def_Bridges_BerggrenTrees_QuantumBerggrenGates
-- name    : Bridges_BerggrenTrees_QuantumBerggrenGates
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:15:14.708999+00:00
-- url     : https://prove2.me/theorems/adbcef91-ce61-4780-86fe-8e14ab151650
-- title:
--   Aether Catalog definitions — Bridges_BerggrenTrees_QuantumBerggrenGates
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenTrees.QuantumBerggrenGates`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenTrees/QuantumBerggrenGates.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Bridges.QuantumBerggrenGates

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 33
-/

noncomputable section

open Matrix

/-- Berggren matrix M₁ -/
def berggrenMat1 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, -2, 2; 2, -1, 2; 2, -2, 3]

/-- Berggren matrix M₂ -/
def berggrenMat2 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 2, 2; 2, 1, 2; 2, 2, 3]

/-- Berggren matrix M₃ -/
def berggrenMat3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, 2, 2; -2, 1, 2; -2, 2, 3]

/-- The signature (2,1) quadratic form matrix: diag(1,1,-1) -/
def sigMat : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; 0, 1, 0; 0, 0, -1]
















def rootVec : Fin 3 → ℤ := ![3, 4, 5]














end


