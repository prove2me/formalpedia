-- Prove2me | Theorems.Thm_exists_pow_smul_eq_and_not_dvd
-- name    : exists_pow_smul_eq_and_not_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:13.860582+00:00
-- url     : https://prove2.me/theorems/9d3b20ec-0e9b-4cda-ae3a-a75b7dc085dd
-- title:
--   exists pow smul eq and not dvd: exists pow smul eq and not dvd
-- statement:
--   The exists pow smul eq and not dvd construction uses the exists pow smul eq and not dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L355-L375
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L355-L375

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
open Finset

theorem exists_pow_smul_eq_and_not_dvd
    {ι : Type*} [Finite ι] (f : ι → ℤ) (hf : f ≠ 0) (p : ℕ) (hp : p ≠ 1) :
    ∃ (n : ℕ) (f' : ι → ℤ), (f = p ^ n • f') ∧ ∃ i, ¬ ↑p ∣ f' i := by sorry
