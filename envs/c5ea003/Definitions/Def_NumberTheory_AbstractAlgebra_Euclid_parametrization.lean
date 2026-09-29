-- Prove2me | Definitions.Def_NumberTheory_AbstractAlgebra_Euclid_parametrization
-- name    : NumberTheory_AbstractAlgebra_Euclid_parametrization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:40.015283+00:00
-- url     : https://prove2.me/theorems/3807722e-f922-4cbb-8e32-033f952420db
-- title:
--   Aether Catalog definitions — NumberTheory_AbstractAlgebra_Euclid_parametrization
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.AbstractAlgebra.Euclid.parametrization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/AbstractAlgebra/Euclid_parametrization.lean by skeleton subtraction
import Mathlib

/-- A Pythagorean triple over the integers (supplied here: the catalog module that originally
provided it is not part of this repository). -/
def IsPythTriple' (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

/-! # CatalogBuild.Shared.Euclid_parametrization

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1
-/


