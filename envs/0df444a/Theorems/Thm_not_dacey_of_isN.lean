-- Prove2me | Theorems.Thm_not_dacey_of_isN
-- name    : not_dacey_of_isN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:06:47.233545+00:00
-- url     : https://prove2.me/theorems/1327fd37-77b2-4fc4-b608-d74c365e44fa
-- title:
--   not dacey of is N: not dacey of is N
-- statement:
--   If P contains an N, then its incomparability orthoset is not Dacey
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L215-L299
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L215-L299

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]

theorem not_dacey_of_isN [Finite P] {a b c d : P} (hN : IsN a b c d) :
    ¬ IsDacey P := by sorry
