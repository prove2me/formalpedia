-- Prove2me | Definitions.Def_Algebra_IntegerEnergy_CryptographyApplications
-- name    : Algebra_IntegerEnergy_CryptographyApplications
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:22:07.573787+00:00
-- url     : https://prove2.me/theorems/75cfa89f-ce40-4643-ac47-80bbbf13d51e
-- title:
--   Aether Catalog definitions — Algebra_IntegerEnergy_CryptographyApplications
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.IntegerEnergy.CryptographyApplications`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/IntegerEnergy/CryptographyApplications.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Computation.CryptographyApplications

Auto-generated from theorem catalog database.
Domain: Computation
Declarations: 14
-/























/-- Hamming distance on Fin n → Bool -/
def hammingDistance {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card


