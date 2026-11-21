-- Prove2me | Theorems.Thm_hasX_iff_hasCoveringX
-- name    : hasX_iff_hasCoveringX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:07:11.452438+00:00
-- url     : https://prove2.me/theorems/1717cec8-7bb1-4772-9222-8f5df8439a18
-- title:
--   has X iff has Covering X: has X iff has Covering X
-- statement:
--   A finite poset contains an X iff it contains a covering X
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L559-L610
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L559-L610

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]

theorem hasX_iff_hasCoveringX [Finite P] :
    (∃ a b c d m : P, IsX a b c d m) ↔
    (∃ a b c d m : P, IsCoveringX a b c d m) := by sorry
