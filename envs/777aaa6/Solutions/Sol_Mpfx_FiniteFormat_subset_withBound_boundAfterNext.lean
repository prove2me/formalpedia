-- Prove2me | solution 1 for Mpfx.FiniteFormat.subset_withBound_boundAfterNext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:29:12.151721+00:00
-- url     : https://prove2.me/submissions/a979ce64-f084-4c09-a905-2d1df0db4fc9

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next
import Theorems.Thm_Mpfx_Format_withBound_mono
import Theorems.Thm_Mpfx_boundOK_boundAfterNext_of_boundOK

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace FiniteFormat
theorem _root_.solution (F : FiniteFormat) :
    F.toFormat ⊆ F.toFormat.withBound F.toFormat.boundAfterNext :=
  Format.withBound_mono F.toFormat (b := F.b) fun _ => boundOK_boundAfterNext_of_boundOK
end FiniteFormat
end Mpfx
