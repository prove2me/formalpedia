-- Prove2me | Definitions.Def_Geometry_Stereographic_TrainingTheory
-- name    : Geometry_Stereographic_TrainingTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:18.4759+00:00
-- url     : https://prove2.me/theorems/784fab96-564f-48a5-ab14-3838e02f1ef0
-- title:
--   Aether Catalog definitions — Geometry_Stereographic_TrainingTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Stereographic.TrainingTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Stereographic/TrainingTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Geometry.Stereographic.TrainingTheory

Auto-generated from theorem catalog database.
Domain: Geometry/Stereographic
Declarations: 13
-/


noncomputable section

/-- The stereographic conformal factor. -/
def stereoConfFactor' (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  2 / (1 + ∑ i, (x i) ^ 2)




/-- [Section: # CatalogBuild.Geometry.Stereographic.TrainingTheory
Auto-generated from theorem catalog database.
Domain: Geometry/Stereographic
Declarations: 13] -/
def stereoLearningRate (baseRate : ℝ) (step : ℕ) : ℝ :=
  baseRate / Real.sqrt (1 + step)












def stereoEffectiveDim (n : ℕ) : ℕ := n + 1












def standardGradMagnitude (qNorm kNorm sqrtD : ℝ) : ℝ :=
  qNorm * kNorm / sqrtD




def stereoGradMagnitude (d : ℕ) (x : Fin d → ℝ) : ℝ :=
  stereoConfFactor' d x












def sphericalRegularizer (seqLen d : ℕ) (X : Fin seqLen → Fin d → ℝ)
    (invStereo : (Fin d → ℝ) → Fin (d + 1) → ℝ) : ℝ :=
  let meanKernel := (∑ i : Fin seqLen, ∑ j : Fin seqLen,
    ∑ k, invStereo (X i) k * invStereo (X j) k) / (seqLen ^ 2 : ℝ)
  meanKernel ^ 2








end


