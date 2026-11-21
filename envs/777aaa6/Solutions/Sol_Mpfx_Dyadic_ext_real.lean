-- Prove2me | solution 1 for Mpfx.Dyadic.ext_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:44.781816+00:00
-- url     : https://prove2.me/submissions/db68637a-42df-4338-95d9-a1c058cc4190

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
theorem _root_.solution {a b : Dyadic} (h : ((a : Dyadic) : ℝ) = ((b : Dyadic) : ℝ)) : a = b := by
  apply Subtype.ext
  exact_mod_cast h
end Mpfx.Dyadic
