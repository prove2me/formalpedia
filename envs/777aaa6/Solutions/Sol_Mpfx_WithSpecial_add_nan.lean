-- Prove2me | solution 1 for Mpfx.WithSpecial.add_nan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:11.908284+00:00
-- url     : https://prove2.me/submissions/0ee6d92e-5004-409d-abdb-845eafb2929f

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution (u : WithSpecial Dyadic) : u + special .nan = special .nan := by
  rcases u with _ | (_ | _) <;> rfl
end Mpfx.WithSpecial
