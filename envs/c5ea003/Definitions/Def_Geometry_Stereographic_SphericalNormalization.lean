-- Prove2me | Definitions.Def_Geometry_Stereographic_SphericalNormalization
-- name    : Geometry_Stereographic_SphericalNormalization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:15.058405+00:00
-- url     : https://prove2.me/theorems/a8249a15-32d2-4679-9612-dc3fbaf41d89
-- title:
--   Aether Catalog definitions — Geometry_Stereographic_SphericalNormalization
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Stereographic.SphericalNormalization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Stereographic/SphericalNormalization.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Geometry.Stereographic.SphericalNormalization

Auto-generated from theorem catalog database.
Domain: Geometry/Stereographic
Declarations: 8
-/


noncomputable section

/-- Squared norm of a vector. -/
def vecSqNorm (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, (v i) ^ 2








/-- The stereographic spherical normalization: project to Sⁿ⁺¹ via inverse
stereographic projection, providing an extra dimension for "confidence". -/
def stereoSphericalNorm (n : ℕ) (v : Fin n → ℝ) : Fin (n + 1) → ℝ := fun i =>
  let D := 1 + vecSqNorm n v
  if h : i.val < n then
    2 * v ⟨i.val, h⟩ / D
  else
    (vecSqNorm n v - 1) / D
















/-- Exponential map normalization: a smooth normalization that uses the
exponential map on the sphere. Given a base point p ∈ Sⁿ and a
tangent vector v ∈ TₚSⁿ, this produces a point on the sphere.
For the south pole base point, this reduces to inverse stereographic
projection (up to reparameterization). -/
def expMapNorm (θ : ℝ) (v : Fin 2 → ℝ) : Fin 3 → ℝ := fun i =>
  let norm_v := Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2)
  match i with
  | ⟨0, _⟩ => if norm_v = 0 then 0 else Real.sin (θ * norm_v) * v 0 / norm_v
  | ⟨1, _⟩ => if norm_v = 0 then 0 else Real.sin (θ * norm_v) * v 1 / norm_v
  | ⟨2, _⟩ => Real.cos (θ * norm_v)








end


