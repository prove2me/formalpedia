-- Prove2me | Definitions.Def_Geometry_Stereographic_GaugeTheory
-- name    : Geometry_Stereographic_GaugeTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:59.888047+00:00
-- url     : https://prove2.me/theorems/372b9b0f-77a3-4379-ac43-68db467eb7f1
-- title:
--   Aether Catalog definitions — Geometry_Stereographic_GaugeTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Stereographic.GaugeTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Stereographic/GaugeTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Geometry.Stereographic.GaugeTheory

Auto-generated from theorem catalog database.
Domain: Geometry/Stereographic
Declarations: 20
-/


noncomputable section

/-- [Section: # CatalogBuild.Geometry.Stereographic.GaugeTheory
Auto-generated from theorem catalog database.
Domain: Geometry/Stereographic
Declarations: 20] -/
def gaugeField (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  2 / (1 + ∑ i, (x i) ^ 2)
















def gaugeInvariantKernel (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  gaugeField n x * gaugeField n y *
    (4 * ∑ i, x i * y i + (∑ i, (x i) ^ 2 - 1) * (∑ i, (y i) ^ 2 - 1))








def gaugeConnection (n : ℕ) (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  -2 * x i / (1 + ∑ j, (x j) ^ 2)












def gaugeCurvatureComponent (n : ℕ) (x : Fin n → ℝ) (i j : Fin n) : ℝ :=
  let D := 1 + ∑ k, (x k) ^ 2
  (if i = j then -2 * D + 4 * (x i) ^ 2 else 4 * x i * x j) / D ^ 2












def gaugeCovariantGrad (n : ℕ) (x : Fin n → ℝ)
    (grad : Fin n → ℝ) (fval : ℝ) : Fin n → ℝ :=
  fun i => grad i + gaugeConnection n x i * fval








def gaugeAction (seqLen n : ℕ) (X : Fin seqLen → Fin n → ℝ) : ℝ :=
  ∑ i : Fin seqLen, ∑ j : Fin seqLen,
    (gaugeField n (X i) * gaugeField n (X j)) ^ 2








def effectiveMass (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  1 / gaugeField n x
















end


