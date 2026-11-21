-- Prove2me | Theorems.Thm_perp_iff
-- name    : perp_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:06:21.959066+00:00
-- url     : https://prove2.me/theorems/feb15d28-49cc-4ee8-87e2-cc3755168755
-- title:
--   perp iff: perp iff
-- statement:
--   For partial orders, ⊥ unfolds to the incomparability condition
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L26-L27
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L26-L27

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true

theorem perp_iff {P : Type*} [PartialOrder P] (a b : P) :
    (a ⊥ b) ↔ ¬ a ≤ b ∧ ¬ b ≤ a := by sorry
