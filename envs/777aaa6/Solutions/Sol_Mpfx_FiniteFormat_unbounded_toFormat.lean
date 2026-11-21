-- Prove2me | solution 1 for Mpfx.FiniteFormat.unbounded_toFormat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:22:48.596175+00:00
-- url     : https://prove2.me/submissions/9fbee6d7-08b7-41a7-b407-94b39060fe23

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) :
    F.unbounded.toFormat = F.toFormat.unbounded := rfl
end Mpfx.FiniteFormat
