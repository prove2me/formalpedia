-- Prove2me | solution 1 for Mpfx.WithSpecial.inf_add_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:18.914227+00:00
-- url     : https://prove2.me/submissions/384d7dcd-d8d2-4a51-987c-fdc56e9113f8

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution (a b : Bool) :
    (special (.inf a) : WithSpecial Dyadic) + special (.inf b) =
      if a = b then special (.inf a) else special .nan := rfl
end Mpfx.WithSpecial
