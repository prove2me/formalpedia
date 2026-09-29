-- Prove2me | Definitions.Def_EML_SPBExtended_SpectralReciprocity
-- name    : EML_SPBExtended_SpectralReciprocity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:53.963584+00:00
-- url     : https://prove2.me/theorems/a8b9074f-d8ab-4473-b8cd-c1b2d2aae6b6
-- title:
--   Aether Catalog definitions — EML_SPBExtended_SpectralReciprocity
-- statement:
--   Definition bundle for the Aether Catalog module `EML.SPBExtended.SpectralReciprocity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/SPBExtended/SpectralReciprocity.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Bridges.SpectralReciprocity

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 10
-/

noncomputable section



/-- Partial Euler product. -/
def partialEulerProduct (f : ℕ → ℂ) (primes : Finset ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ primes, (1 - f p * (↑p : ℂ) ^ (-s))⁻¹








end


