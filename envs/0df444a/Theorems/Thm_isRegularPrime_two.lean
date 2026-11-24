-- Prove2me | Theorems.Thm_isRegularPrime_two
-- name    : isRegularPrime_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:40:04.862667+00:00
-- url     : https://prove2.me/theorems/e99dc764-b8f2-493c-8ab0-7e52313601fd
-- title:
--   is Regular Prime two: is Regular Prime two
-- statement:
--   The is Regular Prime two construction uses the is Regular Prime two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/RegularPrimes.lean#L66-L66
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/RegularPrimes.lean#L66-L66

module
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Definitions.Def_FltRegular_NumberTheory_Cyclotomic_Rat
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open Nat Polynomial NumberField
open scoped NumberField
variable (n p : ℕ)
variable (K : Type*) [Field K]
variable (L : Type*) [Field L] [Algebra K L]

theorem isRegularPrime_two : IsRegularPrime 2 := by sorry
