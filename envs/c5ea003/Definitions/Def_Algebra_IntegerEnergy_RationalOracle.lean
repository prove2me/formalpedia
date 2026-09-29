-- Prove2me | Definitions.Def_Algebra_IntegerEnergy_RationalOracle
-- name    : Algebra_IntegerEnergy_RationalOracle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:21:08.094521+00:00
-- url     : https://prove2.me/theorems/ae94a0ac-507f-4c84-ba26-6254c3883cfa
-- title:
--   Aether Catalog definitions — Algebra_IntegerEnergy_RationalOracle
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.IntegerEnergy.RationalOracle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/IntegerEnergy/RationalOracle.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Computation.Oracles.RationalOracle

Auto-generated from theorem catalog database.
Domain: Computation/Oracles
Declarations: 5
-/










/-- Predicate: n is a sum of two squares. -/
def IsSumOfTwoSquares (n : ℕ) : Prop := ∃ a b : ℕ, a ^ 2 + b ^ 2 = n


