-- Prove2me | Theorems.Thm_isRegularPrime_of_isPrincipalIdealRing
-- name    : isRegularPrime_of_isPrincipalIdealRing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:46.558347+00:00
-- url     : https://prove2.me/theorems/568dbe60-8d07-4421-9599-fa31458adc47
-- title:
--   is Regular Prime of is Principal Ideal Ring: is Regular Prime of is Principal Ideal Ring
-- statement:
--   If the ring of integers of the `p`-th cyclotomic field is a principal ideal ring, then `p` is
--   a regular prime.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/RegularPrimes.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/NumberTheory/RegularPrimes.lean#L38-L41

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

theorem isRegularPrime_of_isPrincipalIdealRing [IsPrincipalIdealRing (𝓞 (CyclotomicField p ℚ))] :
    IsRegularPrime p := by sorry
