-- Prove2me | Theorems.Thm_isRegularPrime_three
-- name    : isRegularPrime_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:40:15.430642+00:00
-- url     : https://prove2.me/theorems/db097057-5a8f-4b83-a3d4-e77c2867d699
-- title:
--   is Regular Prime three: is Regular Prime three
-- statement:
--   The is Regular Prime three construction uses the is Regular Prime three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/RegularPrimes.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/RegularPrimes.lean#L68-L70

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

theorem isRegularPrime_three : IsRegularPrime 3 := by sorry
