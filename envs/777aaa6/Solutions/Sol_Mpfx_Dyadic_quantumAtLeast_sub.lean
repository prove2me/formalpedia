-- Prove2me | solution 1 for Mpfx.Dyadic.quantumAtLeast_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:31:15.229835+00:00
-- url     : https://prove2.me/submissions/ee4b84d8-3548-45e2-a7ba-c95e99bb11d6

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_add

set_option autoImplicit true
open Mpfx
open Mpfx.Dyadic
namespace Mpfx.Dyadic
theorem _root_.solution {e : QExp} {a b : Dyadic}
    (ha : Dyadic.quantumAtLeast e a) (hb : Dyadic.quantumAtLeast e b) :
    Dyadic.quantumAtLeast e (a - b) := by
  rw [sub_eq_add_neg]; exact quantumAtLeast_add ha (Dyadic.quantumAtLeast_neg hb)
end Mpfx.Dyadic
