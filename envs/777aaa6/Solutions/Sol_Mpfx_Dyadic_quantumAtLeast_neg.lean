-- Prove2me | solution 1 for Mpfx.Dyadic.quantumAtLeast_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:28:32.077409+00:00
-- url     : https://prove2.me/submissions/8e7083c2-3f52-4309-9f24-ff1fdbdb9141

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {e : QExp} {x : Dyadic} (h : quantumAtLeast e x) :
    quantumAtLeast e (-x) := by
  cases e using QExp.recBotCoe with
  | bot => trivial
  | coe e =>
    obtain ⟨c, hx⟩ := h
    refine ⟨-c, ?_⟩
    push_cast [Subring.coe_neg, hx]; ring
end Mpfx.Dyadic
