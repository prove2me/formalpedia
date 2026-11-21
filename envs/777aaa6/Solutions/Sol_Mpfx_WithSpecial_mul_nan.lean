-- Prove2me | solution 1 for Mpfx.WithSpecial.mul_nan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:01.244228+00:00
-- url     : https://prove2.me/submissions/87d9a44f-d973-4209-8a54-03c94c1607f0

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution (u : WithSpecial Dyadic) : u * special .nan = special .nan := by
  rcases u with _ | (_ | _) <;> rfl
end Mpfx.WithSpecial
