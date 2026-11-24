-- Prove2me | Theorems.Thm_zeta_sub_one_dvd_trace_sub_smul
-- name    : zeta_sub_one_dvd_trace_sub_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:27.672415+00:00
-- url     : https://prove2.me/theorems/3b323d89-c0c6-4ca3-a38b-d29a944f2ed5
-- title:
--   zeta sub one dvd trace sub smul: zeta sub one dvd trace sub smul
-- statement:
--   The zeta sub one dvd trace sub smul construction uses the zeta sub one dvd trace sub smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L68-L85
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L68-L85

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
open NumberField.RingOfIntegers

theorem zeta_sub_one_dvd_trace_sub_smul (x : 𝓞 K) :
    (hζ.toInteger - 1 : 𝓞 K) ∣ Algebra.trace ℤ _ x - (p - 1) • x := by sorry
