-- Prove2me | solution 1 for Mpfx.Dyadic.quantumAtLeast_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:27:53.406071+00:00
-- url     : https://prove2.me/submissions/d4ce0443-4cb5-4324-a4ca-cb11feb52a76

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
theorem _root_.solution (e : ℤ) (x : Dyadic) :
    quantumAtLeast (e : QExp) x ↔
      ∃ c : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e := Iff.rfl
end Mpfx.Dyadic
