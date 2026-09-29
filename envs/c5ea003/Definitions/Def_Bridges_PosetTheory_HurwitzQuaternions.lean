-- Prove2me | Definitions.Def_Bridges_PosetTheory_HurwitzQuaternions
-- name    : Bridges_PosetTheory_HurwitzQuaternions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:50.187829+00:00
-- url     : https://prove2.me/theorems/58f8ea63-460d-48e3-9114-cb24c1354c02
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_HurwitzQuaternions
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.HurwitzQuaternions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/HurwitzQuaternions.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Computation.Factoring.HurwitzQuaternions

Auto-generated from theorem catalog database.
Domain: Computation/Factoring
Declarations: 27
-/

/-- The sum-of-squares lattice condition. -/
def InSumSqLattice (N : ℤ) (x y z : ℤ) : Prop :=
  N ∣ (x^2 + y^2 + z^2)




/-- The 4D lattice condition. -/
def InSumSqLattice4 (N : ℤ) (a b c d : ℤ) : Prop :=
  N ∣ (a^2 + b^2 + c^2 + d^2)
















/-- A Pythagorean quadruple is primitive if gcd(a, b, c, d) = 1. -/
def IsPrimitiveQuadruple (a b c d : ℕ) : Prop :=
  a^2 + b^2 + c^2 = d^2 ∧ Nat.gcd (Nat.gcd a b) (Nat.gcd c d) = 1


