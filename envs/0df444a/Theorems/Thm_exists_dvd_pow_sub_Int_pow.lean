-- Prove2me | Theorems.Thm_exists_dvd_pow_sub_Int_pow
-- name    : exists_dvd_pow_sub_Int_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:21.443187+00:00
-- url     : https://prove2.me/theorems/b48ec469-09b6-44c8-904e-80617d3ce07b
-- title:
--   exists dvd pow sub Int pow: exists dvd pow sub Int pow
-- statement:
--   The exists dvd pow sub Int pow construction uses the exists dvd pow sub Int pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L33-L44

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
include hp

theorem exists_dvd_pow_sub_Int_pow (a : 𝓞 K) : ∃ b : ℤ, ↑p ∣ a ^ p - (b : 𝓞 K) ^ p := by sorry
