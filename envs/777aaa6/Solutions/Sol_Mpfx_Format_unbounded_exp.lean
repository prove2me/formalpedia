-- Prove2me | solution 1 for Mpfx.Format.unbounded_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:22:15.431229+00:00
-- url     : https://prove2.me/submissions/562535ff-4f69-4d5a-b80d-ed6087c7aa16

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution (F : Format) : F.unbounded.exp = F.exp := rfl
end Mpfx.Format
