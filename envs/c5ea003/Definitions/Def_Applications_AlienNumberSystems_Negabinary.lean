-- Prove2me | Definitions.Def_Applications_AlienNumberSystems_Negabinary
-- name    : Applications_AlienNumberSystems_Negabinary
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:53.210702+00:00
-- url     : https://prove2.me/theorems/a4d14804-dacc-43d5-8928-23c28c76b061
-- title:
--   Aether Catalog definitions — Applications_AlienNumberSystems_Negabinary
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AlienNumberSystems.Negabinary`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AlienNumberSystems/Negabinary.lean by skeleton subtraction
import Mathlib

/-!
# Negabinary: unique finite representations of all integers

This file proves that evaluation in radix `-2` gives a bijection between canonical
finite bit strings and the integers. Digits are stored least-significant first.
-/

namespace Negabinary

/-- The integer represented by a least-significant-first list of bits in base `-2`. -/
def value : List Bool → ℤ
  | [] => 0
  | b :: bs => (if b then 1 else 0) - 2 * value bs

/-- A representation is canonical when it has no zero in its most-significant place. -/
def Canonical (l : List Bool) : Prop := l.getLast? ≠ some false

/-- The forced least-significant bit of an integer. -/
def bit (z : ℤ) : Bool := decide (z % 2 = 1)

/-- The integer value, either zero or one, of the forced bit. -/
def digit (z : ℤ) : ℤ := if bit z then 1 else 0

/-- The quotient remaining after removing the forced digit and dividing by `-2`. -/
def next (z : ℤ) : ℤ := -((z - digit z) / 2)
















end Negabinary


