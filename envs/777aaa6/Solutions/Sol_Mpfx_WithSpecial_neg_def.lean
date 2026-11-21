-- Prove2me | solution 1 for Mpfx.WithSpecial.neg_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:24:40.389163+00:00
-- url     : https://prove2.me/submissions/3d27fbc0-0e3f-428e-9bd8-d6eca07610a7

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference

set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial
namespace Mpfx.WithSpecial
theorem _root_.solution {α : Type} [Neg α] (v : WithSpecial α) : -v = v.neg := rfl
end Mpfx.WithSpecial
