-- Prove2me | solution 1 for Mpfx.WithSpecial.nan_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:23:57.992797+00:00
-- url     : https://prove2.me/submissions/4d0e820f-cf76-4181-a75d-d74e8a706264

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution (v : WithSpecial Dyadic) :
    (special .nan : WithSpecial Dyadic) * v = special .nan := by
  rcases v with _ | (_ | _) <;> rfl
end Mpfx.WithSpecial
