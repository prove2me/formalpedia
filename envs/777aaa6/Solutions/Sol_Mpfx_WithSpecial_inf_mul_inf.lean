-- Prove2me | solution 1 for Mpfx.WithSpecial.inf_mul_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:01.766176+00:00
-- url     : https://prove2.me/submissions/97aca33a-80ab-4b87-9ec3-f28967e8c0f6

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution (a b : Bool) :
    (special (.inf a) : WithSpecial Dyadic) * special (.inf b) = special (.inf (xor a b)) :=
  rfl
end Mpfx.WithSpecial
