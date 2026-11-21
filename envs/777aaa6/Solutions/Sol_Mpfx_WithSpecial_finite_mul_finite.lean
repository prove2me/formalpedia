-- Prove2me | solution 1 for Mpfx.WithSpecial.finite_mul_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:23:57.48564+00:00
-- url     : https://prove2.me/submissions/967f38bf-b8de-46d2-b0a3-1b32f396057c

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution (x y : Dyadic) :
    finite x * finite y = finite (x * y) := rfl
end Mpfx.WithSpecial
