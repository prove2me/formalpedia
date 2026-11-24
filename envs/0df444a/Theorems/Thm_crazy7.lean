-- Prove2me | Theorems.Thm_crazy7
-- name    : crazy7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:18.64423+00:00
-- url     : https://prove2.me/theorems/d68ec37d-85e5-4d45-85d9-d9ee7cd3df7d
-- title:
--   crazy7: crazy7
-- statement:
--   The explicit floor computation used in the Minkowski bound for the seventh cyclotomic field.
--
--   Source: https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Seven/Seven.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/flt-regular/blob/69c70f28505f8431496e0cf4b158b97b1863cced/FltRegular/SmallNumbers/Seven/Seven.lean#L32-L45

module
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_FltRegular_SmallNumbers_Seven_Seven
set_option autoImplicit false
@[expose] public section
public section
open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers
  IsCyclotomicExtension.Rat Polynomial cyclotomic Ideal
variable {K : Type*} [Field K] [NumberField K]
local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

theorem crazy7 : ⌊(4 / π) ^ 3 * (6! / 6 ^ 6 * √16807)⌋₊ = 4 := by sorry
