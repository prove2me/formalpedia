-- Prove2me | Theorems.Thm_exists_not_isPrincipal_and_isPrincipal_map_aux
-- name    : exists_not_isPrincipal_and_isPrincipal_map_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:35.541802+00:00
-- url     : https://prove2.me/theorems/1d749c9a-9a68-4e2b-8407-90d16762913e
-- title:
--   exists not is Principal and is Principal map aux: exists not is Principal and is Principal map aux
-- statement:
--   The exists not is Principal and is Principal map aux construction uses the exists not is Principal and is Principal map aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert94.lean#L51-L80
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert94.lean#L51-L80

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
include hσ
open FiniteDimensional

theorem exists_not_isPrincipal_and_isPrincipal_map_aux
    [IsDedekindDomain A] [Algebra.Unramified A B] (η : Bˣ)
    (hη : Algebra.norm K (algebraMap B L η) = 1)
    (hη' : ¬∃ α : Bˣ, algebraMap B L η = (algebraMap B L α) / σ (algebraMap B L α)) :
    ∃ I : Ideal A, ¬I.IsPrincipal ∧ (I.map (algebraMap A B)).IsPrincipal := by sorry
