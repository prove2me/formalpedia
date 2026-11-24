-- Prove2me | Theorems.Thm_zeta_sub_one_pow_dvd_norm_sub_pow
-- name    : zeta_sub_one_pow_dvd_norm_sub_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:31.557798+00:00
-- url     : https://prove2.me/theorems/a482158d-b526-4a4b-8696-12f87e56557b
-- title:
--   zeta sub one pow dvd norm sub pow: zeta sub one pow dvd norm sub pow
-- statement:
--   The zeta sub one pow dvd norm sub pow construction uses the zeta sub one pow dvd norm sub pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L87-L110
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L87-L110

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

theorem zeta_sub_one_pow_dvd_norm_sub_pow (x : 𝓞 K) :
    (hζ.toInteger - 1 : 𝓞 K) ^ p ∣
      (Algebra.norm ℤ (1 + p • x) : 𝓞 K) - 1 + p • x := by sorry
