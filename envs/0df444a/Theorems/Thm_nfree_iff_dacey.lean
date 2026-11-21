-- Prove2me | Theorems.Thm_nfree_iff_dacey
-- name    : nfree_iff_dacey
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:07:21.822187+00:00
-- url     : https://prove2.me/theorems/22f585b2-3f56-4b32-9dc6-d0dffca0c6fa
-- title:
--   nfree iff dacey: nfree iff dacey
-- statement:
--   Main theorem: a finite poset is N-free iff its incomparability orthoset is Dacey
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L513-L519
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L513-L519

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]

theorem nfree_iff_dacey [Finite P] : IsNFree P ↔ IsDacey P := by sorry
