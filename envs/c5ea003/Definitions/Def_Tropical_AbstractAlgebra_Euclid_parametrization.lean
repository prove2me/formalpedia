-- Prove2me | Definitions.Def_Tropical_AbstractAlgebra_Euclid_parametrization
-- name    : Tropical_AbstractAlgebra_Euclid_parametrization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:28:46.156568+00:00
-- url     : https://prove2.me/theorems/2d330b7f-9f38-4dc4-898f-3f03d0cb17e1
-- title:
--   Aether Catalog definitions — Tropical_AbstractAlgebra_Euclid_parametrization
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.AbstractAlgebra.Euclid.parametrization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/AbstractAlgebra/Euclid_parametrization.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Euclid_parametrization

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1
-/

/-- A (possibly degenerate) integer Pythagorean triple. -/
def IsPythTriple' (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2


