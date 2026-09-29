-- Prove2me | Definitions.Def_Geometry_Logic_SpectralDescent
-- name    : Geometry_Logic_SpectralDescent
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:40:06.566855+00:00
-- url     : https://prove2.me/theorems/90c1bfaa-85fa-4d8f-88ed-dd19d6499799
-- title:
--   Aether Catalog definitions — Geometry_Logic_SpectralDescent
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Logic.SpectralDescent`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Logic/SpectralDescent.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Logic.SpectralDescent

Auto-generated from theorem catalog database.
Domain: Logic
Declarations: 10
-/

/-- In the monster tower, curves at level k are classified as R, V, or T. -/
inductive RVT where
  | R : RVT  -- Regular
  | V : RVT  -- Vertical
  | T : RVT  -- Tangent
deriving DecidableEq, Repr



noncomputable def conformalFactor (t : ℝ) : ℝ := 4 / (1 + t ^ 2) ^ 2






/-- An oracle at each level of the descent, projecting Fin (k+2) → Fin (k+1). -/
def descentOracle (k : ℕ) : (Fin (k+2) → ℝ) → (Fin (k+1) → ℝ) :=
  fun v => fun i => v ⟨i.val, by omega⟩


