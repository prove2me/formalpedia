-- Prove2me | solution 1 for Fpy.RoundCtx.round_special
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:06:36.309953+00:00
-- url     : https://prove2.me/submissions/4043d333-b7f2-42d2-8b7c-5aa162e7bec3

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Fpy_Ops

set_option autoImplicit true
open Fpy
open Mpfx
open Fpy.RoundCtx
namespace Fpy.RoundCtx
theorem _root_.solution (c : RoundCtx) (s : Special) : c.round (.special s) = (c.S.map s).toReal :=
  rfl
end Fpy.RoundCtx
