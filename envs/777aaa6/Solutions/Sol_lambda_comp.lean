-- Prove2me | solution 1 for lambda_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:00:59.640815+00:00
-- url     : https://prove2.me/submissions/8e84c6e5-f864-49cc-82e4-abdd778b2e20

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc

set_option autoImplicit false
variable {α β γ : Type*}
theorem _root_.solution (f : α → β) (g : β → γ) :
    (fun b ↦ g b) ∘ (fun a ↦ f a) = g ∘ f :=
  rfl
