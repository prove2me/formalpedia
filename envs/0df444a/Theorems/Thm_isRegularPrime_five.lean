-- Prove2me | Theorems.Thm_isRegularPrime_five
-- name    : isRegularPrime_five
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:15:28.755797+00:00
-- url     : https://prove2.me/theorems/f42bceb0-38f6-4fe2-91aa-7a08abf22f73
-- title:
--   is Regular Prime five: is Regular Prime five
-- statement:
--   Five is a regular prime.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Five/FLT5.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Five/FLT5.lean#L20-L22

module
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
public import Definitions.Def_FltRegular_FltRegular
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_SmallNumbers_Five_FLT5
set_option autoImplicit false
@[expose] public section
public section
open Nat NumberField IsCyclotomicExtension

theorem isRegularPrime_five : IsRegularPrime 5 := by sorry
