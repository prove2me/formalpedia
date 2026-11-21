-- Prove2me | solution 1 for Mpfx.Format.withBound_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:39:40.09068+00:00
-- url     : https://prove2.me/submissions/a51e7eec-742c-4a4c-b17d-211bda4ef8ad

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution (F : Format) (b' : Bound) :
    (F.withBound b').p = F.p := rfl
end Mpfx.Format
