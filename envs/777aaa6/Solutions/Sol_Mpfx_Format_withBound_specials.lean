-- Prove2me | solution 1 for Mpfx.Format.withBound_specials
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:39:49.013317+00:00
-- url     : https://prove2.me/submissions/2cf71291-4a56-45f6-b634-7c906c6fc5f8

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution (F : Format) (b' : Bound) :
    (F.withBound b').specials = F.specials := rfl
end Mpfx.Format
