-- Prove2me | Theorems.Thm_norm_eq_prod_pow_gen
-- name    : norm_eq_prod_pow_gen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:42.445639+00:00
-- url     : https://prove2.me/theorems/c12e006f-e628-44b1-ab96-d6e7836d27af
-- title:
--   norm eq prod pow gen: norm eq prod pow gen
-- statement:
--   The norm eq prod pow gen construction uses the norm eq prod pow gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L180-L189
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L180-L189

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

theorem norm_eq_prod_pow_gen
    [IsGalois k K] [FiniteDimensional k K]
    (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) (η : K) :
    algebraMap k K (Algebra.norm k η) = (∏ i ∈ Finset.range (orderOf σ), (σ ^ i) η) := by sorry
