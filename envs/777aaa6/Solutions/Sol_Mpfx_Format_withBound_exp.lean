-- Prove2me | solution 1 for Mpfx.Format.withBound_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:39:37.859961+00:00
-- url     : https://prove2.me/submissions/8fd8fbad-d59b-48d1-949c-4c1fb5281234

import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_Format_Next

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution (F : Format) (b' : Bound) :
    (F.withBound b').exp = F.exp := rfl
end Mpfx.Format
