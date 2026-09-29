-- Prove2me | Definitions.Def_Bridges_KeplerDefs
-- name    : Bridges_KeplerDefs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:30.783979+00:00
-- url     : https://prove2.me/theorems/7a472bc2-ccaf-4bef-9a6a-2d79cadda3eb
-- title:
--   Aether Catalog definitions — Bridges_KeplerDefs
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.KeplerDefs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/KeplerDefs.lean by skeleton subtraction
import Mathlib
/-
  # Kepler Problem — Core Definitions

  Fundamental definitions for the Kepler/two-body problem:
  eccentricity, semi-latus rectum, semi-major axis,
  effective potential, and circular orbit radius.
-/

open Real

/-- The eccentricity of a Kepler orbit: e = √(1 + 2El²/(mk²)). -/
noncomputable def keplerEccentricity (m k E l : ℝ) : ℝ :=
  Real.sqrt (1 + 2 * E * l ^ 2 / (m * k ^ 2))

/-- The semi-latus rectum: p = l²/(mk). -/
noncomputable def semiLatusRectum (m k l : ℝ) : ℝ :=
  l ^ 2 / (m * k)


