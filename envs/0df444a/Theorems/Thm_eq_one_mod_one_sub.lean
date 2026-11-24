-- Prove2me | Theorems.Thm_eq_one_mod_one_sub
-- name    : eq_one_mod_one_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:51.054392+00:00
-- url     : https://prove2.me/theorems/b8c2828d-36ba-49e9-a70b-a8a2bf2cab1c
-- title:
--   eq one mod one sub: eq one mod one sub
-- statement:
--   The eq one mod one sub construction uses the eq one mod one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/UnitLemmas.lean#L32-L34
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/UnitLemmas.lean#L32-L34

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

theorem eq_one_mod_one_sub {A : Type*} [CommRing A] {t : A} :
    algebraMap A (A ⧸ Ideal.span ({t - 1} : Set A)) t = 1 := by sorry
