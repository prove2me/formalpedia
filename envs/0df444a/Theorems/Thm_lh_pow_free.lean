-- Prove2me | Theorems.Thm_lh_pow_free
-- name    : lh_pow_free
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:38:07.714852+00:00
-- url     : https://prove2.me/theorems/0657ae60-783e-4c2e-a4fd-e4fba23c1093
-- title:
--   lh pow free: lh pow free
-- statement:
--   The lh pow free construction uses the lh pow free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L455-L465
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L455-L465

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

theorem lh_pow_free (ν : (𝓞 k)ˣ)
    (hk : ∀ (ε : (𝓞 k)ˣ) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε)
    (η : Fin (NumberField.Units.rank k + 2) → Additive (𝓞 k)ˣ) :
    ∃ (a : ℤ) (ι : Fin (NumberField.Units.rank k + 2) → ℤ)
      (i₀ : Fin (NumberField.Units.rank k + 2)),
      ∑ i, ι i • η i = (a * p) • Additive.ofMul ν ∧
        ¬ (p : ℤ) ∣ ι i₀ ∧ (ν = 1 → i₀ ≠ Fin.last _) := by sorry
