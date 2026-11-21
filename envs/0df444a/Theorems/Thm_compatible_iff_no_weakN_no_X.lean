-- Prove2me | Theorems.Thm_compatible_iff_no_weakN_no_X
-- name    : compatible_iff_no_weakN_no_X
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:08:13.659498+00:00
-- url     : https://prove2.me/theorems/bf5e889d-b9eb-4e18-b1b9-2bb1b0c95a1d
-- title:
--   compatible iff no weak N no X: compatible iff no weak N no X
-- statement:
--   Main theorem: for a finite poset P, the following are equivalent:
--       (a) P contains no weak N and no X
--       (b) P has a compatible incomparability orthoset
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L911-L938
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L911-L938

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]

theorem compatible_iff_no_weakN_no_X [Finite P] :
    IsCompatible P ↔
    (¬ ∃ a b c d : P, IsWeakN a b c d) ∧
    (¬ ∃ a b c d m : P, IsX a b c d m) := by sorry
