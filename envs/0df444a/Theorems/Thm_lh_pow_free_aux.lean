-- Prove2me | Theorems.Thm_lh_pow_free_aux
-- name    : lh_pow_free_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:46.210987+00:00
-- url     : https://prove2.me/theorems/dad6d00e-e9c0-4286-b322-f33bdd097af7
-- title:
--   lh pow free aux: lh pow free aux
-- statement:
--   The lh pow free aux construction uses the lh pow free aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L378-L391
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L378-L391

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
include hp

theorem lh_pow_free_aux {M} [CommGroup M] [Module.Finite ℤ (Additive M)] (ν : M)
    (hk : ∀ (ε : M) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε)
    (r) (hr : finrank ℤ (Additive M) < r) (η : Fin r → Additive M) :
    ∃ (a : ℤ) (ι : Fin r → ℤ) (i : Fin r),
      ∑ i, ι i • η i = a • (Additive.ofMul ν) ∧ ¬ ↑p ∣ ι i := by sorry
