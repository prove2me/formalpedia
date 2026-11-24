-- Prove2me | Theorems.Thm_systemOfUnits_isMaximal
-- name    : systemOfUnits.isMaximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:34:13.691969+00:00
-- url     : https://prove2.me/theorems/5df83a88-80a9-4bba-902a-ba8dc402f71e
-- title:
--   system Of Units: is Maximal
-- statement:
--   A full-rank system of units is maximal.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L33-L40

module
public import Definitions.Def_FltRegular_NumberTheory_SystemOfUnits
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Henselian
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField nonZeroDivisors
open FiniteDimensional NumberField
variable {s r : ℕ} (p : ℕ) {K : Type*} [Field K]
variable {k : Type*} [Field k] (hp : Nat.Prime p)
open Module Finset
open CyclotomicIntegers (zeta)
variable (G : Type*) [AddCommGroup G]
local notation3 "A" => CyclotomicIntegers p
include hp

theorem systemOfUnits.isMaximal [Module.Finite ℤ G] (hf : finrank ℤ G = s * (p - 1))
  [Module A G] (sys : systemOfUnits (G := G) p s) : sys.IsMaximal := by sorry
