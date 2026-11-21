-- Prove2me | solution 1 for Mpfx.WithSpecial.finite_add_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:35.633531+00:00
-- url     : https://prove2.me/submissions/ff8d743d-721d-4f04-a328-f7f8f04424a9

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution (x : Dyadic) (b : Bool) :
    finite x + special (.inf b) = special (.inf b) := rfl
end Mpfx.WithSpecial
