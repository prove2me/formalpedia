-- Prove2me | Theorems.Thm_MulAction_mem_stabilizer_pi
-- name    : MulAction.mem_stabilizer_pi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:46:01.941197+00:00
-- url     : https://prove2.me/theorems/42f4b67e-f8ad-49ad-abec-563ee66f2583
-- title:
--   Mul Action: mem stabilizer pi
-- statement:
--   The Mul Action construction uses the mem stabilizer pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L163-L166
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L163-L166

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem MulAction.mem_stabilizer_pi {ι : Type*} {α : ι → Type*} {G : Type*} [Group G]
    [∀ i, MulAction G (α i)] (x : ∀ i, α i) (g : G) :
    g ∈ MulAction.stabilizer G x ↔ ∀ i, g ∈ MulAction.stabilizer G (x i) := by sorry
