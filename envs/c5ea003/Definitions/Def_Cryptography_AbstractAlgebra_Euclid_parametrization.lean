-- Prove2me | Definitions.Def_Cryptography_AbstractAlgebra_Euclid_parametrization
-- name    : Cryptography_AbstractAlgebra_Euclid_parametrization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:02:47.086773+00:00
-- url     : https://prove2.me/theorems/9cfebcd8-786f-4837-94bd-725a89c859ef
-- title:
--   Aether Catalog definitions — Cryptography_AbstractAlgebra_Euclid_parametrization
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.AbstractAlgebra.Euclid.parametrization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/AbstractAlgebra/Euclid_parametrization.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Euclid_parametrization

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1
-/


/-- `(a, b, c)` is a Pythagorean triple. -/
def IsPythTriple' (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2


