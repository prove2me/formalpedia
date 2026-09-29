-- Prove2me | Definitions.Def_Novelty_AbstractAlgebra_Euclid_parametrization
-- name    : Novelty_AbstractAlgebra_Euclid_parametrization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T13:59:02.595857+00:00
-- url     : https://prove2.me/theorems/6216eb1a-38a4-4b40-9712-e3386126f8ba
-- title:
--   Aether Catalog definitions — Novelty_AbstractAlgebra_Euclid_parametrization
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AbstractAlgebra.Euclid.parametrization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AbstractAlgebra/Euclid_parametrization.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Euclid_parametrization

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1
-/

/-- A Pythagorean triple (primed variant) (supplied here: the catalog module that originally provided it is not part of this repository) -/
def IsPythTriple' (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

/-- A Pythagorean triple (supplied here: the catalog module that originally provided it is not part of this repository) -/
def IsPythTriple (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2


