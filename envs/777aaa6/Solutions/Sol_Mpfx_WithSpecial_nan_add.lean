-- Prove2me | solution 1 for Mpfx.WithSpecial.nan_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:11.485621+00:00
-- url     : https://prove2.me/submissions/80c38c75-4607-4a35-a849-8253eeb87d98

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution (v : WithSpecial Dyadic) :
    (special .nan : WithSpecial Dyadic) + v = special .nan := by
  rcases v with _ | (_ | _) <;> rfl
end Mpfx.WithSpecial
