-- Prove2me | Theorems.Thm_almostHilbert92
-- name    : almostHilbert92
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:35.06552+00:00
-- url     : https://prove2.me/theorems/d1491649-e915-4e54-bd4e-1c9af64f43ee
-- title:
--   almost Hilbert92: almost Hilbert92
-- statement:
--   The almost Hilbert92 construction uses the almost Hilbert92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L622-L735
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L622-L735

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
variable
    [Algebra k K] (hKL : finrank k K = p) (σ : K ≃ₐ[k] K)
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
local notation "mkG" => unitToU p hp hKL σ hσ
variable [NumberField k]
variable [NumberField K]
variable [IsGalois k K]
attribute [local instance] _p2m_local_instance_fee6646a52_507
attribute [local instance] _p2m_local_instance_fee6646a52_512
attribute [local instance] _p2m_local_instance_fee6646a52_515
variable [IsUnramifiedAtInfinitePlaces k K]
local notation "r" => NumberField.Units.rank k
include hp hKL hσ

theorem almostHilbert92 (hpodd : p ≠ 2) : ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧
      ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := by sorry
