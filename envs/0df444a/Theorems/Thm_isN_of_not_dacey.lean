-- Prove2me | Theorems.Thm_isN_of_not_dacey
-- name    : isN_of_not_dacey
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:06:52.98078+00:00
-- url     : https://prove2.me/theorems/0a25ce1e-81d3-4125-9235-1ac5ebe0dfcc
-- title:
--   is N of not dacey: is N of not dacey
-- statement:
--   If the incomparability orthoset of P is not Dacey, then P contains an N
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L310-L510
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L310-L510

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]

theorem isN_of_not_dacey [Finite P] (hD : ¬ IsDacey P) :
    ∃ a b c d : P, IsN a b c d := by sorry
