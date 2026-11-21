-- Prove2me | solution 1 for Mpfx.Dyadic.quantumAtLeast_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:26:00.465854+00:00
-- url     : https://prove2.me/submissions/96eb2c67-8112-4728-a255-17fa6b3a9ce4

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_two_zpow_shift


set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {e₁ e₂ : QExp} (h : e₂ ≤ e₁) {x : Dyadic}
    (hx : quantumAtLeast e₁ x) : quantumAtLeast e₂ x := by
  cases e₂ using QExp.recBotCoe with
  | bot => trivial
  | coe e₂ =>
    cases e₁ using QExp.recBotCoe with
    | bot => exact absurd (le_bot_iff.mp h) (WithBot.coe_ne_bot)
    | coe e₁ =>
      obtain ⟨c, hc⟩ := hx
      exact ⟨_, hc.trans (Mpfx.two_zpow_shift c (WithBot.coe_le_coe.mp h))⟩
end Mpfx.Dyadic
