-- Prove2me | Theorems.Thm_norm_add_one_smul_of_isUnit
-- name    : norm_add_one_smul_of_isUnit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:32.580888+00:00
-- url     : https://prove2.me/theorems/485bd48b-cb4a-4720-a6f9-b1df37a8730d
-- title:
--   norm add one smul of is Unit: norm add one smul of is Unit
-- statement:
--   The norm add one smul of is Unit construction uses the norm add one smul of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L112-L127
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean#L112-L127

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

theorem norm_add_one_smul_of_isUnit {K} [Field K] [NumberField K] {p : ℕ} (hpri : p.Prime)
    (hp : p ≠ 2) (x : 𝓞 K)
    (hx : IsUnit (1 + p • x)) : Algebra.norm ℤ (1 + p • x) = 1 := by sorry
