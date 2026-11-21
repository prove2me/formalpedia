-- Prove2me | Theorems.Thm_not_compatible_if_X
-- name    : not_compatible_if_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:07:19.014701+00:00
-- url     : https://prove2.me/theorems/c59cc0c6-1a25-426f-8464-221a67058cea
-- title:
--   not compatible if X: not compatible if X
-- statement:
--   If a finite poset P contains an X, then P is not compatible
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L654-L694
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L654-L694

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]

theorem not_compatible_if_X [Finite P] (a b c d m : P) (h : IsX a b c d m) :
    ¬ IsCompatible P := by sorry
