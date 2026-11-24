-- Prove2me | Theorems.Thm_dvd_card_classGroup_of_unramified_isCyclic
-- name    : dvd_card_classGroup_of_unramified_isCyclic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:40.538351+00:00
-- url     : https://prove2.me/theorems/f03c66b7-2bea-40ee-a8b6-8ef3365b1205
-- title:
--   dvd card class Group of unramified is Cyclic: dvd card class Group of unramified is Cyclic
-- statement:
--   This is the second part of **Hilbert Theorem 94**, which states that if `L/K` is an unramified
--     cyclic finite extension of number fields of odd prime degree,
--     then the degree divides the class number of `K`.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert94.lean#L110-L119
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert94.lean#L110-L119

module
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Definitions.Def_FltRegular_NumberTheory_Hilbert92
public import Definitions.Def_FltRegular_NumberTheory_Unramified
public import Definitions.Def_FltRegular_NumberTheory_Hilbert94
public import Theorems.Thm_Hilbert92

set_option autoImplicit false
@[expose] public section
public section
open scoped NumberField
variable {K : Type} [Field K]
open Polynomial Module
variable {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ)
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
    [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L]
variable [IsGalois K L]

theorem dvd_card_classGroup_of_unramified_isCyclic {K L : Type}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra.Unramified (𝓞 K) (𝓞 L)]
    [IsCyclic (L ≃ₐ[K] L)] (hKL : Nat.Prime (finrank K L)) (hKL' : finrank K L ≠ 2) :
    finrank K L ∣ Fintype.card (ClassGroup (𝓞 K)) := by sorry
