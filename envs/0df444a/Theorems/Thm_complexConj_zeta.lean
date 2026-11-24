-- Prove2me | Theorems.Thm_complexConj_zeta
-- name    : complexConj_zeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:35:27.986437+00:00
-- url     : https://prove2.me/theorems/0a02175e-fe07-4766-ae7b-96f6a1f1c813
-- title:
--   complex Conj zeta: complex Conj zeta
-- statement:
--   The complex Conj zeta construction uses the complex Conj zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/UnitLemmas.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/UnitLemmas.lean#L41-L49

module
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_UnitLemmas
set_option autoImplicit false
@[expose] public section
public section
variable {p : ℕ} [NeZero p] {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open IsCyclotomicExtension NumberField Polynomial IsCMField
noncomputable section
local notation3 "η" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
set_option quotPrecheck false
local notation "I" => (Ideal.span ({(η - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))
variable [NumberField K] [IsCyclotomicExtension {p} ℚ K]
include hζ

theorem complexConj_zeta [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    complexConj K ζ = ζ⁻¹ := by sorry
