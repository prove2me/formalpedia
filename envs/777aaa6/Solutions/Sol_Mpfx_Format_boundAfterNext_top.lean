-- Prove2me | solution 1 for Mpfx.Format.boundAfterNext_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:39:39.611736+00:00
-- url     : https://prove2.me/submissions/da1e9f6e-ef79-4742-a439-0f7db68f866d

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F : Format} (hF : F.b = ⊤) :
    F.boundAfterNext = ⊤ := by unfold boundAfterNext; rw [hF]
end Mpfx.Format
