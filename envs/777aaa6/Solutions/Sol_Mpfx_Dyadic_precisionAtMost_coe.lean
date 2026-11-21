-- Prove2me | solution 1 for Mpfx.Dyadic.precisionAtMost_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:25:59.940881+00:00
-- url     : https://prove2.me/submissions/4c9489ad-f40b-495c-ae54-2126f5bf5a0c

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
theorem _root_.solution (p : ℕ) (x : Dyadic) :
    precisionAtMost (p : Prec) x ↔
      ∃ c e : ℤ, (x : ℚ) = (c : ℚ) * (2 : ℚ) ^ e ∧ |c| < (2 : ℤ) ^ p := Iff.rfl
end Mpfx.Dyadic
