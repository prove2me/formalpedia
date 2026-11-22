-- Prove2me | Theorems.Thm_MulAction_stabilizer_fun_const
-- name    : MulAction.stabilizer_fun_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:45:42.061677+00:00
-- url     : https://prove2.me/theorems/aede63a2-6089-4e76-b274-199f6d80b4f8
-- title:
--   Mul Action: stabilizer fun const
-- statement:
--   The Mul Action construction uses the stabilizer fun const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L151-L155
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L151-L155

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem MulAction.stabilizer_fun_const {α : Type*} (ι G : Type*) [Nonempty ι] [Group G]
    [MulAction G α] (x : α) :
    MulAction.stabilizer G (fun _ : ι ↦ x) = MulAction.stabilizer G x := by sorry
