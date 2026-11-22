-- Prove2me | Theorems.Thm_MulAction_stabilizer_pi
-- name    : MulAction.stabilizer_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:54:48.352168+00:00
-- url     : https://prove2.me/theorems/fbe580cf-91c9-44bc-a05e-5f4aa9c5f03b
-- title:
--   Mul Action: stabilizer pi
-- statement:
--   The Mul Action construction uses the stabilizer pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L157-L161
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L157-L161

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem MulAction.stabilizer_pi {ι : Type*} {α : ι → Type*} (G : Type*) [Group G]
    [∀ i, MulAction G (α i)] (x : ∀ i, α i) :
    MulAction.stabilizer G x = ⨅ i, MulAction.stabilizer G (x i) := by sorry
