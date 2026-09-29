-- Prove2me | Definitions.Def_Geometry_Logic_DimensionalProjection
-- name    : Geometry_Logic_DimensionalProjection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:40:06.510856+00:00
-- url     : https://prove2.me/theorems/8340bcc1-6098-49b0-a0fb-d2c1a9215c37
-- title:
--   Aether Catalog definitions — Geometry_Logic_DimensionalProjection
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Logic.DimensionalProjection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Logic/DimensionalProjection.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Logic.DimensionalProjection

Auto-generated from theorem catalog database.
Domain: Logic
Declarations: 30
-/

noncomputable section

/-- Forward stereographic projection from S¹ to ℝ.
Projects from the north pole (0, -1). Given (x, y) on S¹ with y ≠ -1,
maps to t = x / (1 + y). -/
def stereoForward1 (x y : ℝ) : ℝ := x / (1 + y)

/-- Inverse stereographic projection from ℝ to S¹. -/
def invStereo1 (t : ℝ) : ℝ × ℝ :=
  (2 * t / (1 + t ^ 2), (1 - t ^ 2) / (1 + t ^ 2))





/-- Forward stereographic projection from S² to ℝ².
Projects from north pole (0, 0, -1).
Given (x, y, z) on S² with z ≠ -1, maps to (x/(1+z), y/(1+z)). -/
def stereoForward2 (x y z : ℝ) : ℝ × ℝ :=
  (x / (1 + z), y / (1 + z))

/-- Inverse stereographic projection from ℝ² to S².
Given (u, v) ∈ ℝ², maps to S² via:
(2u/(1+u²+v²), 2v/(1+u²+v²), (1-u²-v²)/(1+u²+v²)) -/
def invStereo2 (u v : ℝ) : ℝ × ℝ × ℝ :=
  let d := 1 + u ^ 2 + v ^ 2
  (2 * u / d, 2 * v / d, (1 - u ^ 2 - v ^ 2) / d)




/-- Inverse stereographic projection from ℝ³ to S³.
Given (u, v, w) ∈ ℝ³, maps to S³. -/
def invStereo3 (u v w : ℝ) : Fin 4 → ℝ := fun i =>
  let d := 1 + u ^ 2 + v ^ 2 + w ^ 2
  match i with
  | 0 => 2 * u / d
  | 1 => 2 * v / d
  | 2 => 2 * w / d
  | 3 => (1 - u ^ 2 - v ^ 2 - w ^ 2) / d



/-- One step of the ascending ladder: ℝ → S¹ ↪ ℝ² → S².
Start with t ∈ ℝ, map to S¹ via inv_stereo, embed in ℝ²,
then lift to S² via inv_stereo again. -/
def liftRtoS2 (t : ℝ) : ℝ × ℝ × ℝ :=
  let p := invStereo1 t  -- ℝ → S¹
  invStereo2 p.1 p.2     -- ℝ² → S²
















end


