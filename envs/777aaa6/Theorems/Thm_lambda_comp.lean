-- Prove2me | Theorems.Thm_lambda_comp
-- name    : lambda_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:54:11.10881+00:00
-- url     : https://prove2.me/theorems/f3b3b3d1-c10d-41e0-86d6-7680a628c4bc
-- title:
--   lambda comp: lambda comp
-- statement:
--   The lambda comp construction uses the lambda comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L39-L41
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L39-L41

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {α β γ : Type*}

theorem lambda_comp (f : α → β) (g : β → γ) :
    (fun b ↦ g b) ∘ (fun a ↦ f a) = g ∘ f := by sorry
