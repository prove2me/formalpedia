-- Prove2me | Definitions.Def_Bridges_SpectralReciprocity
-- name    : Bridges_SpectralReciprocity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:38.636266+00:00
-- url     : https://prove2.me/theorems/654eca5a-1250-4156-8ddd-6ab383107903
-- title:
--   Aether Catalog definitions — Bridges_SpectralReciprocity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.SpectralReciprocity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/SpectralReciprocity.lean by skeleton subtraction
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


