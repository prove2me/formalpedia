-- Prove2me | solution 1 for Mpfx.WithSpecial.finite_mul_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:08.006994+00:00
-- url     : https://prove2.me/submissions/7552f370-a783-4190-ae6a-286a51b6e0a0

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution (x : Dyadic) (b : Bool) :
    finite x * special (.inf b) =
      if x = 0 then special .nan else special (.inf (xor b (decide ((x : ℚ) < 0)))) := rfl
end Mpfx.WithSpecial
