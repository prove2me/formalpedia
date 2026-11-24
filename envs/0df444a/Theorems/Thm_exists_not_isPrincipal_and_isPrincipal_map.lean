-- Prove2me | Theorems.Thm_exists_not_isPrincipal_and_isPrincipal_map
-- name    : exists_not_isPrincipal_and_isPrincipal_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:59.506407+00:00
-- url     : https://prove2.me/theorems/417b87bd-0a7d-438f-95c1-5fe21bf006cf
-- title:
--   exists not is Principal and is Principal map: exists not is Principal and is Principal map
-- statement:
--   This is the first part of **Hilbert Theorem 94**, which states that if `L/K` is an unramified
--     cyclic finite extension of number fields of odd prime degree,
--     then there is an ideal that capitulates in `K`.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert94.lean#L97-L105
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert94.lean#L97-L105

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

theorem exists_not_isPrincipal_and_isPrincipal_map (K L : Type)
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra.Unramified (𝓞 K) (𝓞 L)]
    [h : IsCyclic (L ≃ₐ[K] L)] (hKL : Nat.Prime (finrank K L)) (hKL' : finrank K L ≠ 2) :
    ∃ I : Ideal (𝓞 K), ¬I.IsPrincipal ∧
      (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by sorry
