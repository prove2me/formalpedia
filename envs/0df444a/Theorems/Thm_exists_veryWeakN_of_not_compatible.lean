-- Prove2me | Theorems.Thm_exists_veryWeakN_of_not_compatible
-- name    : exists_veryWeakN_of_not_compatible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:07:49.311472+00:00
-- url     : https://prove2.me/theorems/347bf6c9-c8f3-47c9-b53d-966bb75aa1aa
-- title:
--   exists very Weak N of not compatible: exists very Weak N of not compatible
-- statement:
--   Every incompatible poset contains a very weak N
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L734-L751
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L734-L751

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]

theorem exists_veryWeakN_of_not_compatible (hP : ¬ IsCompatible P) :
    ∃ a b c d : P, IsVeryWeakN a b c d := by sorry
