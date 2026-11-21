-- Prove2me | solution 1 for Mpfx.Format.withBound_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:39:48.512752+00:00
-- url     : https://prove2.me/submissions/0dcca6b8-9cc5-44d6-8ea8-c3054bf5b5e7

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution (F : Format) (b' : Bound) :
    (F.withBound b').b = b' := rfl
end Mpfx.Format
