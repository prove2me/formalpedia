-- Prove2me | solution 1 for Mpfx.Format.unbounded_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:22:15.929494+00:00
-- url     : https://prove2.me/submissions/88bbbb12-8433-42be-a068-ac7fb6c8a32d

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution (F : Format) :
    F.unbounded.unbounded = F.unbounded := rfl
end Mpfx.Format
