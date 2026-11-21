-- Prove2me | solution 1 for Mpfx.WithSpecial.inf_add_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:33.259373+00:00
-- url     : https://prove2.me/submissions/1cdb1b95-457b-48e1-8704-abae4f760d7d

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution (a : Bool) (y : Dyadic) :
    (special (.inf a) : WithSpecial Dyadic) + finite y = special (.inf a) := rfl
end Mpfx.WithSpecial
