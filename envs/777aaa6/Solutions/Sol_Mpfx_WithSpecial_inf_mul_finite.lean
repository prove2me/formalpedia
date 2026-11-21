-- Prove2me | solution 1 for Mpfx.WithSpecial.inf_mul_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:04.977846+00:00
-- url     : https://prove2.me/submissions/71004caa-1706-4e30-aff9-fab0a5150cab

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution (a : Bool) (y : Dyadic) :
    (special (.inf a) : WithSpecial Dyadic) * finite y =
      if y = 0 then special .nan else special (.inf (xor a (decide ((y : ℚ) < 0)))) := rfl
end Mpfx.WithSpecial
