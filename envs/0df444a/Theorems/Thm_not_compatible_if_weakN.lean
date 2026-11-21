-- Prove2me | Theorems.Thm_not_compatible_if_weakN
-- name    : not_compatible_if_weakN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:06:19.94957+00:00
-- url     : https://prove2.me/theorems/4f9d7bfe-acea-4629-af82-ccb2d2146f19
-- title:
--   not compatible if weak N: not compatible if weak N
-- statement:
--   If a poset contains a weak N, then it is not compatible
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L615-L651
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L615-L651

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]

theorem not_compatible_if_weakN (a b c d : P) (h : IsWeakN a b c d) :
    ¬ IsCompatible P := by sorry
