-- Prove2me | Definitions.Def_Algebra_Computation_CryptographyApplications
-- name    : Algebra_Computation_CryptographyApplications
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:10:50.105039+00:00
-- url     : https://prove2.me/theorems/85cdc213-3e3d-476c-9b80-0c0638b268a3
-- title:
--   Aether Catalog definitions — Algebra_Computation_CryptographyApplications
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.Computation.CryptographyApplications`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/Computation/CryptographyApplications.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Computation.CryptographyApplications

Auto-generated from theorem catalog database.
Domain: Computation
Declarations: 14
-/























/-- Hamming distance on Fin n → Bool -/
def hammingDistance {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card


