-- Prove2me | Theorems.Thm_systemOfUnits_IsFundamental_corollary
-- name    : systemOfUnits.IsFundamental.corollary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:37:25.609263+00:00
-- url     : https://prove2.me/theorems/840a33dd-22b3-465d-abe9-71c85d66b3f8
-- title:
--   Is Fundamental: corollary
-- statement:
--   The Is Fundamental construction uses the corollary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L139-L160
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert92.lean#L139-L160

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

theorem systemOfUnits.IsFundamental.corollary [Module A G] (S : systemOfUnits p G s) (hs : S.IsFundamental) (a : Fin s → ℤ)
    (ha : ∃ i, ¬ (p : ℤ) ∣ a i) :
    ∀ g : G, (1 - zeta p) • g ≠ ∑ i, a i • S.units i := by sorry
