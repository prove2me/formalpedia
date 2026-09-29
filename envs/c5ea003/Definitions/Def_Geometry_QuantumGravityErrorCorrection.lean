-- Prove2me | Definitions.Def_Geometry_QuantumGravityErrorCorrection
-- name    : Geometry_QuantumGravityErrorCorrection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:50.343983+00:00
-- url     : https://prove2.me/theorems/2449f8c1-92cd-415b-99e7-9d90a07cb1c3
-- title:
--   Aether Catalog definitions — Geometry_QuantumGravityErrorCorrection
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.QuantumGravityErrorCorrection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/QuantumGravityErrorCorrection.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Physics.Spacetime.QuantumGravityErrorCorrection

Auto-generated from theorem catalog database.
Domain: Physics/Spacetime
Declarations: 17
-/

noncomputable section

/-- [Section: # CatalogBuild.Physics.Spacetime.QuantumGravityErrorCorrection
Auto-generated from theorem catalog database.
Domain: Physics/Spacetime
Declarations: 17] -/
structure QECCode where
  n : ℕ
  k : ℕ
  d : ℕ
  valid : k ≤ n
  distance_bound : d ≤ n - k + 1

/-- [Section: # CatalogBuild.Physics.Spacetime.QuantumGravityErrorCorrection
Auto-generated from theorem catalog database.
Domain: Physics/Spacetime
Declarations: 17] -/
def QECCode.rate (C : QECCode) : ℝ := (C.k : ℝ) / (C.n : ℝ)


def correctableErrors (d : ℕ) : ℕ := (d - 1) / 2


structure PerfectTensor where
  legs : ℕ
  bond_dim : ℕ
  even_legs : legs % 2 = 0
  dim_pos : bond_dim ≥ 2

def PerfectTensor.maxEntropy (T : PerfectTensor) : ℝ :=
  (T.legs / 2 : ℝ) * Real.log (T.bond_dim : ℝ)






def allowedWavenumber (n : ℕ) (L : ℝ) : ℝ := 2 * Real.pi * (n : ℝ) / L





end


