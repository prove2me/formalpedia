-- Prove2me | solution 1 for Mpfx.WithSpecial.finite_add_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:08.483321+00:00
-- url     : https://prove2.me/submissions/25b3e133-7acf-4ae2-845c-2acf50b425f4

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution (x y : Dyadic) :
    finite x + finite y = finite (x + y) := rfl
end Mpfx.WithSpecial
