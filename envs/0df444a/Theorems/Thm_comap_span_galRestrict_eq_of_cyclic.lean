-- Prove2me | Theorems.Thm_comap_span_galRestrict_eq_of_cyclic
-- name    : comap_span_galRestrict_eq_of_cyclic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:48.458673+00:00
-- url     : https://prove2.me/theorems/4b5d6414-f045-46d3-8e17-8a43cdf628bd
-- title:
--   comap span gal Restrict eq of cyclic: comap span gal Restrict eq of cyclic
-- statement:
--   The comap span gal Restrict eq of cyclic construction uses the comap span gal Restrict eq of cyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert94.lean#L25-L45
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Hilbert94.lean#L25-L45

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
include hσ

theorem comap_span_galRestrict_eq_of_cyclic (β : B) (η : Bˣ)
    (hβ : η * (galRestrict A K L B σ) β = β) (σ' : L ≃ₐ[K] L) :
    (Ideal.span {β}).comap (galRestrict A K L B σ') = Ideal.span {β} := by sorry
