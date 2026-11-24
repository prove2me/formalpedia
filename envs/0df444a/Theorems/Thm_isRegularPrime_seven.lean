-- Prove2me | Theorems.Thm_isRegularPrime_seven
-- name    : isRegularPrime_seven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:15:09.673524+00:00
-- url     : https://prove2.me/theorems/9e5c8f9a-a3a7-47ef-a875-f0c8c72e1285
-- title:
--   is Regular Prime seven: is Regular Prime seven
-- statement:
--   Seven is a regular prime.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Seven/FLT7.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Seven/FLT7.lean#L21-L23

module
public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_FltRegular
public import Definitions.Def_FltRegular_NumberTheory_RegularPrimes
public import Definitions.Def_FltRegular_SmallNumbers_Seven_Seven
public import Definitions.Def_FltRegular_SmallNumbers_Seven_FLT7
set_option autoImplicit false
@[expose] public section
public section
open Nat NumberField IsCyclotomicExtension

theorem isRegularPrime_seven : IsRegularPrime 7 := by sorry
