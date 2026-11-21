-- Prove2me | solution 1 for Mpfx.Format.mem_toSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:23:31.269234+00:00
-- url     : https://prove2.me/submissions/3a0ff074-542c-4b71-9ba3-3d328f71e53f

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise
namespace Mpfx.Format
theorem _root_.solution {F : Format} {x : Dyadic} :
    x ∈ F.toSet ↔ x ∈ F := Iff.rfl
end Mpfx.Format
