-- Prove2me | Theorems.Thm_quotient_zero_sub_one_comp_aut
-- name    : quotient_zero_sub_one_comp_aut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:18.641283+00:00
-- url     : https://prove2.me/theorems/4c720270-557f-46d7-85f1-73c9e7761e96
-- title:
--   quotient zero sub one comp aut: quotient zero sub one comp aut
-- statement:
--   The quotient zero sub one comp aut construction uses the quotient zero sub one comp aut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L46-L65
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L46-L65

module
public import Mathlib.RingTheory.NormTrace
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_MoreLemmas
set_option autoImplicit false
@[expose] public section
public section
variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat
variable (hp : p ≠ 2)

theorem quotient_zero_sub_one_comp_aut (σ : 𝓞 K →+* 𝓞 K) :
    (Ideal.Quotient.mk (Ideal.span {(hζ.toInteger : 𝓞 K) - 1})).comp σ =
      Ideal.Quotient.mk _ := by sorry
