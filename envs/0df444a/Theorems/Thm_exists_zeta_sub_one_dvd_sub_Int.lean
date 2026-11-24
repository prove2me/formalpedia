-- Prove2me | Theorems.Thm_exists_zeta_sub_one_dvd_sub_Int
-- name    : exists_zeta_sub_one_dvd_sub_Int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:50.496646+00:00
-- url     : https://prove2.me/theorems/06b5ba44-df96-425b-bdae-c6640271da60
-- title:
--   exists zeta sub one dvd sub Int: exists zeta sub one dvd sub Int
-- statement:
--   The exists zeta sub one dvd sub Int construction uses the exists zeta sub one dvd sub Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L27-L30

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

theorem exists_zeta_sub_one_dvd_sub_Int (a : 𝓞 K) :
    ∃ b : ℤ, (hζ.toInteger - 1 : 𝓞 K) ∣ a - b := by sorry
