-- Prove2me | solution 1 for Mpfx.FiniteFormat.extend_toFormat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:38:31.740994+00:00
-- url     : https://prove2.me/submissions/b7a264c5-053f-4fad-ac2c-f394db0ebd59

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) k :
    (F.extend k).toFormat = F.toFormat.extend k := rfl
end Mpfx.FiniteFormat
