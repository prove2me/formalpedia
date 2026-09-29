-- Prove2me | Definitions.Def_Geometry_QuotientSpaces
-- name    : Geometry_QuotientSpaces
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:54.565732+00:00
-- url     : https://prove2.me/theorems/360b9f73-bb1b-4d73-b409-7d37bf662e24
-- title:
--   Aether Catalog definitions — Geometry_QuotientSpaces
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.QuotientSpaces`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/QuotientSpaces.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Geometry.SphericalUniverse.QuotientSpaces

Auto-generated from theorem catalog database.
Domain: Geometry/SphericalUniverse
Declarations: 26
-/


noncomputable section

/-- The volume of the quotient S³/Γ. -/
def volumeQuotient (R : ℝ) (groupOrder : ℕ) : ℝ :=
  2 * Real.pi ^ 2 * R ^ 3 / groupOrder












/-- A lens space L(p, q) has group order p. -/
def lensSpaceOrder (p : ℕ) : ℕ := p




/-- The volume of lens space L(p, q). -/
def volumeLensSpace (R : ℝ) (p : ℕ) : ℝ := volumeQuotient R p








/-- Simplified degeneracy for L(p, 1). -/
def lensSpaceDegeneracy (p ℓ : ℕ) : ℕ :=
  if p = 0 then 0
  else ((ℓ + 1) ^ 2 + p - 1) / p












/-- The binary icosahedral group I* has order 120. -/
def binaryIcosahedralOrder : ℕ := 120




/-- The volume of PDS. -/
def volumePDS (R : ℝ) : ℝ := volumeQuotient R binaryIcosahedralOrder








/-- The first few ℓ values contributing to the PDS spectrum.
ℓ = 2, 3, 4, 5 are ABSENT — this suppresses low CMB multipoles! -/
def pdsAllowedModes : List ℕ := [0, 6, 10, 12, 15, 16, 18, 20, 21, 22, 24, 25, 26, 27, 28, 30]














/-- [Section: # CatalogBuild.Geometry.SphericalUniverse.QuotientSpaces
Auto-generated from theorem catalog database.
Domain: Geometry/SphericalUniverse
Declarations: 26] -/
def binaryTetrahedralOrder : ℕ := 24



def binaryOctahedralOrder : ℕ := 48








/-- Matched circle pairs for S³/Γ. -/
def matchedCirclePairs (groupOrder : ℕ) : ℕ := groupOrder - 1




























end


