-- Prove2me | Definitions.Def_NumberTheory_SumsOfThreeCubes
-- name    : NumberTheory_SumsOfThreeCubes
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:15.085666+00:00
-- url     : https://prove2.me/theorems/ec6abee5-2306-4436-98ae-690ab5b1c47d
-- title:
--   Aether Catalog definitions — NumberTheory_SumsOfThreeCubes
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.SumsOfThreeCubes`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/SumsOfThreeCubes.lean by skeleton subtraction
import Mathlib

/-!
# Sums of Three Cubes: the Exact Modulo-Nine Obstruction

This file proves that reduction modulo nine gives exactly one obstruction:
a residue is a sum of three cubes in `ZMod 9` precisely when it is not `4`
or `5`. It also records global consequences, sign symmetry, a polynomial
family of integral points, and the corresponding affine-cubic-surface view.
-/

namespace SumsOfThreeCubes

/-- An integer is globally representable by three integral cubes. -/
def Representable (k : ℤ) : Prop :=
  ∃ x y z : ℤ, x ^ 3 + y ^ 3 + z ^ 3 = k

/-- The familiar modulo-nine obstruction. -/
def ForbiddenModNine (k : ℤ) : Prop :=
  k % 9 = 4 ∨ k % 9 = 5

/-- Solvability of the cubic equation after reduction modulo `n`. -/
def LocallyRepresentable (k : ℤ) (n : ℕ) : Prop :=
  ∃ x y z : ZMod n, x ^ 3 + y ^ 3 + z ^ 3 = (k : ZMod n)

/-- The affine cubic surface over a commutative ring. -/
def CubicSurface (R : Type*) [CommRing R] (k : R) : Set (R × R × R) :=
  {p | p.1 ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3 = k}














end SumsOfThreeCubes


