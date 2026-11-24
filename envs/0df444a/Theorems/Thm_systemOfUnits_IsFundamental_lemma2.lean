-- Prove2me | Theorems.Thm_systemOfUnits_IsFundamental_lemma2
-- name    : systemOfUnits.IsFundamental.lemma2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:33.887621+00:00
-- url     : https://prove2.me/theorems/fcf0bc20-9e0d-420f-9a88-5c7c824983a0
-- title:
--   Is Fundamental: lemma2
-- statement:
--   The Is Fundamental construction uses the lemma2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L81-L137
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L81-L137

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
open systemOfUnits systemOfUnits.IsFundamental
variable {H : Type*} [CommGroup H] [Fintype H] (hCard : Fintype.card H = p)
  (σ : H) (hσ : Subgroup.zpowers σ = ⊤) (s : ℕ) [DistribMulAction H G]
  (hf : finrank ℤ G = s * (p - 1))
include hp hf
variable [Module.Finite ℤ G]

theorem systemOfUnits.IsFundamental.lemma2 [Module A G] (S : systemOfUnits p G s) (hs : S.IsFundamental)
    (i : Fin s) (a : Fin s →₀ A) (ha : a i = 1) :
    ∀ g : G, (1 - zeta p) • g ≠ Finsupp.linearCombination A S.units a := by sorry
