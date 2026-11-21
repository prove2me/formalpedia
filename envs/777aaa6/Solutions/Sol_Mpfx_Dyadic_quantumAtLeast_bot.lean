-- Prove2me | solution 1 for Mpfx.Dyadic.quantumAtLeast_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:20:46.387008+00:00
-- url     : https://prove2.me/submissions/23a909ca-6ea7-48a6-aa4c-77c01c322d63

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
theorem _root_.solution (x : Dyadic) : quantumAtLeast ⊥ x := trivial
end Mpfx.Dyadic
